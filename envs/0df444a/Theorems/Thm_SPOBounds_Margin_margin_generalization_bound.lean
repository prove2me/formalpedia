-- Prove2me | Theorems.Thm_SPOBounds_Margin_margin_generalization_bound
-- name    : SPOBounds.Margin.margin_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:35:49.037992+00:00
-- url     : https://prove2.me/theorems/149f2a0a-5027-4822-bd48-fae4061ebf39
-- title:
--   Theorem 4 — margin-based generalization bound for the SPO loss under the strength property ($\ell_2$ case)
-- statement:
--   Work in the $\ell_2$ set-up: decisions in $\mathbb R^d$ with the Euclidean norm, cost vectors with its dual (again Euclidean) norm. Let $S\subseteq\mathbb R^d$ be nonempty, compact, convex and not a singleton, $w^*$ any optimization oracle for $S$, and suppose $S$ satisfies the strength property with parameter $\mu>0$. Fix $\gamma>0$. Let $\mathcal D$ be a probability distribution on feature–cost pairs $(x,c)$ whose cost lies almost surely in a nonempty bounded set $\mathcal C$, and let $\mathcal H$ be a class of functions from $\mathcal X$ to $\mathbb R^d$. Then for every $n\ge1$ and every $\delta>0$, with probability at least $1-\delta$ over an i.i.d. sample $(x_1,c_1),\dots,(x_n,c_n)$ from $\mathcal D$, every $f\in\mathcal H$ satisfies
--   $$R_{\rm SPO}(f)\;\le\;\hat R^\gamma_{\rm SPO}(f)+\Big(\frac{2\sqrt2\,\rho_2(\mathcal C)+2\sqrt2\,\mu\cdot\omega_S(\mathcal C)}{\gamma\mu}\Big)\,\mathfrak R^n(\mathcal H)+\omega_S(\mathcal C)\sqrt{\frac{\log(1/\delta)}{2n}} .$$
--   Here $R_{\rm SPO}$ is the SPO risk, $\hat R^\gamma_{\rm SPO}$ the empirical $\gamma$-margin SPO risk, $\mathfrak R^n(\mathcal H)$ the expected multivariate Rademacher complexity, $\rho_2(\mathcal C)=\sup_{c\in\mathcal C}\|c\|_2$ and $\omega_S(\mathcal C)=\sup_{c\in\mathcal C}\omega_S(c)$.
--
--   This is the paper's margin-based generalization bound: the complexity term is the multivariate Rademacher complexity of $\mathcal H$, which for common classes grows mildly in the dimensions, at the price of the empirical margin loss in place of the empirical SPO loss.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the (outer) measure under $\mathcal D^n$ of the samples on which some $f\in\mathcal H$ violates the bound is at most $\delta$. The cost space carries the Borel $\sigma$-algebra. The paper is silent on measurability; added hypotheses are that every $f\in\mathcal H$ and its SPO loss $(x,c)\mapsto\ell_{\rm SPO}(f(x),c)$ are measurable, that the uniform deviation $\sup_{f}\big(\mathbb E[\ell^\gamma_{\rm SPO}(f(x),c)]-\hat R^\gamma_{\rm SPO}(f)\big)$ and the margin Rademacher suprema are a.e.-measurable in the sample, and that the multivariate Rademacher sums are almost surely bounded above and $\hat{\mathfrak R}^n(\mathcal H)$ is integrable over samples, so that $\mathfrak R^n(\mathcal H)$ is the paper's expectation (when it is infinite the bound is vacuous).
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, pp. 19–20, Theorem 4, second display

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Rademacher

open MeasureTheory

namespace SPOBounds.Margin

/-- **Theorem 4, second display** (arXiv:1905.11488v3, pp. 19–20). ℓ₂ set-up: `E = ℝ^d` with the
Euclidean norm, costs and predictions in its dual (operator norm = Euclidean norm), with the Borel
σ-algebra. Let `S` be nonempty, compact, convex and not a singleton, `w` any oracle, and suppose
`S` satisfies the strength property with parameter `μ > 0`. Fix `γ > 0`, a nonempty bounded set
`C` containing the cost vector almost surely, and any `δ > 0`. Then with probability at least
`1 − δ` over an i.i.d. sample of size `n` from `D`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂^γ_SPO(f) + ((2√2 ρ₂(C) + 2√2 μ ω_S(C)) / (γ μ)) ℜⁿ(H) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is at
most `δ`. Added hypotheses (the paper is silent): measurability of each `f ∈ H` and of its SPO
loss (`hf`, `hℓ`), of the uniform deviation and of the margin Rademacher sups (`hΦ`, `hA`); and
almost-sure boundedness plus integrability of the multivariate empirical Rademacher complexity
(`hBdd`, `hInt`), without which `ℜⁿ(H)` is not the paper's quantity. -/
theorem margin_generalization_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H,
      Measurable (fun z : X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        marginSupDeviation S w γ D H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable
        (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
          marginSignedSup S w γ H σ s)
        (Measure.pi fun _ : Fin n => D))
    (hBdd : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => D), ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (s i).1 (signVec (σ i))))
    (hInt : Integrable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        empRademacherMulti H (fun i => (s i).1))
      (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empMarginRisk S w γ f s +
          (2 * Real.sqrt 2 * rhoSet C + 2 * Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
            expRademacherMulti D H n +
          omegaSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by sorry

end SPOBounds.Margin
