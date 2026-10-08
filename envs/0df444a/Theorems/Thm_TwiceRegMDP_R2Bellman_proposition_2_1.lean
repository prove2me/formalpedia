-- Prove2me | Theorems.Thm_TwiceRegMDP_R2Bellman_proposition_2_1
-- name    : TwiceRegMDP.R2Bellman.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:21:34.9308+00:00
-- url     : https://prove2.me/theorems/2e79063b-0636-4672-ba57-5bb34bd1d64b
-- title:
--   Proposition 2.1 — the conjugate of a strongly convex function on the simplex is smooth, shift-equivariant and monotone
-- statement:
--   Let $\mathcal Z$ be a finite nonempty set and $\Omega:\Delta_{\mathcal Z}\to\mathbb R$ a strongly convex function (with some modulus $m>0$) that is continuous on the simplex, and let $\Omega^*(y)=\max_{a\in\Delta_{\mathcal Z}}\langle a,y\rangle-\Omega(a)$. Then:
--
--   1. $\Omega^*$ is differentiable on $\mathbb R^{\mathcal Z}$, its gradient is Lipschitz, and for every $y$ it is the unique maximizer
--   $$\nabla\Omega^*(y)=\operatorname*{arg\,max}_{a\in\Delta_{\mathcal Z}}\ \langle a,y\rangle-\Omega(a);$$
--   2. for every $c\in\mathbb R$ and $y\in\mathbb R^{\mathcal Z}$, $\Omega^*(y+c\mathbb 1_{\mathcal Z})=\Omega^*(y)+c$;
--   3. $\Omega^*$ is non-decreasing for the pointwise order on $\mathbb R^{\mathcal Z}$.
--
--   These are the properties of the "smoothed max" that make regularized greedy policies well defined and regularized Bellman optimality operators monotone and contracting; the paper cites them from Hiriart-Urruty–Lemaréchal and Mensch–Blondel.
--
--   **Formalization Note.** Strong convexity is Mathlib's `StrongConvexOn` on the simplex with respect to the sup norm of `Z → ℝ`; in finite dimension the class of strongly convex functions does not depend on the norm (only the modulus does), and the statement quantifies over the modulus. Continuity of $\Omega$ on the simplex is an added hypothesis: without it the maximum can fail to be attained (on $\mathcal Z=\{1,2\}$, $\Omega(a)=a_1^2$ except $\Omega(e_1)=5$ is strongly convex, and for $y=(3,0)$ the supremum $2$ is not attained). The nonemptiness of $\mathcal Z$ is implicit in the paper. The gradient is stated as a Fréchet derivative $y'\mapsto\sum_z g(y)(z)\,y'(z)$; Lipschitz continuity is in the sup norm, which is equivalent to any other norm in finite dimension.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 3, Proposition 2.1 (cited from [14, 25])

import Mathlib
import Definitions.Def_TwiceRegMDP_R2Bellman_SimplexConjugate

namespace TwiceRegMDP.R2Bellman

/-- Proposition 2.1 (Derman–Geist–Mannor, arXiv:2110.06267v1, p. 3; cited from [14, 25]).
Let `Ω : Δ_Z → ℝ` be strongly convex (for some modulus `m > 0`) and continuous on the simplex
`Δ_Z` of a finite nonempty set `Z`, and let `Ω^∗(y) = max_{a ∈ Δ_Z} ⟨a, y⟩ − Ω(a)`. Then
(i) `Ω^∗` is differentiable on all of `ℝ^Z`, its gradient `∇Ω^∗(y) = g(y)` is the unique maximizer
of `a ↦ ⟨a, y⟩ − Ω(a)` over `Δ_Z`, and `g` is Lipschitz;
(ii) `Ω^∗(y + c 1_Z) = Ω^∗(y) + c` for all `c ∈ ℝ`, `y ∈ ℝ^Z`;
(iii) `Ω^∗` is non-decreasing (for the pointwise order on `ℝ^Z`). -/
theorem proposition_2_1 {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (Ω : (Z → ℝ) → ℝ) (m : ℝ) (hm : 0 < m) (hΩ : StrongConvexOn (stdSimplex ℝ Z) m Ω)
    (hΩc : ContinuousOn Ω (stdSimplex ℝ Z)) :
    (∃ g : (Z → ℝ) → (Z → ℝ), (∃ K : NNReal, LipschitzWith K g) ∧
      ∀ y : Z → ℝ,
        HasFDerivAt (simplexConj Ω)
          (∑ z, g y z • (ContinuousLinearMap.proj z : (Z → ℝ) →L[ℝ] ℝ)) y ∧
        g y ∈ stdSimplex ℝ Z ∧
        ∀ a ∈ stdSimplex ℝ Z, a ≠ g y →
          ∑ z, a z * y z - Ω a < ∑ z, g y z * y z - Ω (g y)) ∧
    (∀ (c : ℝ) (y : Z → ℝ), simplexConj Ω (fun z => y z + c) = simplexConj Ω y + c) ∧
    Monotone (simplexConj Ω) := by sorry

end TwiceRegMDP.R2Bellman
