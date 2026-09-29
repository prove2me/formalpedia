-- Prove2me | Theorems.Thm_SPOBounds_Margin_margin_rademacher_bound
-- name    : SPOBounds.Margin.margin_rademacher_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:35:01.30856+00:00
-- url     : https://prove2.me/theorems/4b453c26-a1a4-40a8-91b4-f7b6c6e5348f
-- title:
--   Theorem 4, first display — $\hat{\mathfrak R}^n_{\gamma\rm SPO}(\mathcal H)\le\frac{\sqrt2\rho_2(\mathcal C)+\sqrt2\mu\,\omega_S(\mathcal C)}{\gamma\mu}\hat{\mathfrak R}^n(\mathcal H)$
-- statement:
--   Work in the $\ell_2$ set-up: decisions in $\mathbb R^d$ with the Euclidean norm, cost vectors with its dual (again Euclidean) norm. Let $S\subseteq\mathbb R^d$ be nonempty, compact, convex and not a singleton, $w^*$ any optimization oracle for $S$, and suppose $S$ satisfies the strength property with parameter $\mu>0$. Fix $\gamma>0$, a nonempty bounded set $\mathcal C$ of cost vectors with $\rho_2(\mathcal C)=\sup_{c\in\mathcal C}\|c\|_2$ and $\omega_S(\mathcal C)=\sup_{c\in\mathcal C}\omega_S(c)$, and a class $\mathcal H$ of functions from $\mathcal X$ to $\mathbb R^d$. Then for any fixed sample $(x_1,c_1),\dots,(x_n,c_n)$ with $c_i\in\mathcal C$,
--   $$\hat{\mathfrak R}^n_{\gamma\rm SPO}(\mathcal H)\;\le\;\Big(\frac{\sqrt2\,\rho_2(\mathcal C)+\sqrt2\,\mu\cdot\omega_S(\mathcal C)}{\gamma\mu}\Big)\,\hat{\mathfrak R}^n(\mathcal H).$$
--
--   The Rademacher complexity of the margin-loss class is controlled by the multivariate Rademacher complexity of the hypothesis class itself, with no dependence on the structure of $S$ beyond $\mu$ and $\omega_S(\mathcal C)$.
--
--   **Formalization Note** The costs of the sample are required to lie in $\mathcal C$ (the paper's $\mathcal C$ is the domain of the true costs). The multivariate sums over $\mathcal H$ at this sample are assumed bounded above for every sign pattern, so that $\hat{\mathfrak R}^n(\mathcal H)$ is finite; when it is infinite the paper's bound is vacuous. The left-hand side needs no such assumption, since $0\le\ell^\gamma_{\rm SPO}(\hat c,c_i)\le\omega_S(c_i)$.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 19, Theorem 4, first display

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher

namespace SPOBounds.Margin

/-- **Theorem 4, first display** (arXiv:1905.11488v3, p. 19). ℓ₂ set-up: `E = ℝ^d` with the
Euclidean norm. Let `S` be nonempty, compact, convex and not a singleton, `w` any oracle, and
suppose `S` satisfies the strength property with parameter `μ > 0`. Fix `γ > 0`, a nonempty
bounded set `C` of cost vectors, a class `H` of maps from `X` to cost vectors, and a sample
`(x₁, c₁), …, (xₙ, cₙ)` with every `cᵢ ∈ C`. If the multivariate Rademacher sums over `H` are
bounded above for every sign matrix, then
`R̂ⁿ_{γSPO}(H) ≤ ((√2 ρ₂(C) + √2 μ ω_S(C)) / (γ μ)) R̂ⁿ(H)`. -/
theorem margin_rademacher_bound {d n : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (hsC : ∀ i, (s i).2 ∈ C)
    (hB : ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (s i).1 (signVec (σ i)))) :
    empRademacherMargin S w γ H s ≤
      (Real.sqrt 2 * rhoSet C + Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
        empRademacherMulti H (fun i => (s i).1) := by sorry

end SPOBounds.Margin
