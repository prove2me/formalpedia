-- Prove2me | Theorems.Thm_ScholtesStab_step1_display_14
-- name    : ScholtesStab.step1_display_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:26.219175+00:00
-- url     : https://prove2.me/theorems/c292c0e8-3d17-4ff3-8dc4-aa9d0364c9fb
-- title:
--   Proof of Theorem 1, Step 1, display (14): $\alpha-\alpha^{\mathcal S}_t\le|a^0_{01}|+|a^-_{00}|$
-- statement:
--   Let $t_k>0$, $t_k\to0$, and let $x^k$ be Karush–Kuhn–Tucker points of $\mathcal S$ (parameter $t_k$) converging to $\bar x\in M$, where MPCC-LICQ holds. Let $(\bar\sigma,\bar\varrho)$ satisfy (5) at $\bar x$ and NDC2 ($\bar\varrho_{1,j}\bar\varrho_{2,j}>0$ for $j\in a_{00}(\bar x)$). Then for all sufficiently large $k$,
--
--   $$
--   \bigl(|a_{01}(\bar x)|+|a_{10}(\bar x)|+2|a_{00}(\bar x)|\bigr)-\bigl(|\mathcal H(x^k)|+|\mathcal N_1(x^k)|+|\mathcal N_2(x^k)|\bigr)\ \le\ |a^0_{01}(\bar x)|+|a^0_{10}(\bar x)|+|a^-_{00}(\bar x)| .
--   $$
--
--   By Step 1 the left side is the difference of the codimensions $\alpha-\alpha^{\mathcal S}_t$ of $\mathcal T_{\bar x}$ and $\mathcal T^{\mathcal S}_{x^k}$; this bound feeds the lower estimate of the C-index in Step 4.
--
--   **Formalization Note** The inequality is in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
--   - encoding: a sequence xᵗ converging to x̄ for t → 0 ("for all sufficiently small t", "for infinitely many t") → t : ℕ → ℝ with t k > 0 and t k → 0, x k → x̄; ∀ᶠ k in atTop and ∃ᶠ k in atTop; reason: the standard sequential reading of the paper's sequence; t k > 0 because S is defined for t > 0
--   - generalization: (14): α − αˢ_t ≤ |a⁰₀₁(x̄)| + |a⁻₀₀(x̄)| under the proof's assumption a₁₀(x̄) = ∅ (p.18, "without loss of generality") → the general statement with the a₁₀ terms; reason: setting a₁₀(x̄) = ∅ makes the a₁₀ terms vanish and gives the printed claim
--   - generalization: the setting of Theorem 1 (nondegenerate KKT points of quadratic index q, x̄ nondegenerate C-stationary) → KKT points (not necessarily nondegenerate), MPCC-LICQ at x̄, and multipliers with (5) and NDC2; reason: the hypotheses of Theorem 1 imply these (ND, NDC3 and the fixed index q are not used), so the statement specializes to the printed claim
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, Proof of Theorem 1, Step 1, display (14), p.18

import Mathlib
import Definitions.Def_ScholtesStab_MPCC
import Definitions.Def_ScholtesStab_MPCC_a01
import Definitions.Def_ScholtesStab_MPCC_MPCCLICQ
import Definitions.Def_ScholtesStab_MPCC_IsCStationary
import Definitions.Def_ScholtesStab_MPCC_a01neg
import Definitions.Def_ScholtesStab_MPCC_H
import Definitions.Def_ScholtesStab_MPCC_IsKKT

namespace ScholtesStab

open MPCC Filter Topology

/-- **Display (14).** Lämmel–Shikhman, arXiv:2501.07383v2, Proof of Theorem 1, Step 1, p.18:
"We claim that α − αˢ_t ≤ |a⁰₀₁(x̄)| + |a⁻₀₀(x̄)|."

Setting: KKT points `x k` of S with parameters `t k > 0`, `t k → 0`, `x k → x̄ ∈ M`, MPCC-LICQ at
`x̄`, and multipliers `(σ̄, ϱ̄)` of `x̄` satisfying (5) and NDC2. Then for all sufficiently large
`k`, in `ℤ`,
`(|a₀₁(x̄)| + |a₁₀(x̄)| + 2|a₀₀(x̄)|) − (|ℋ(x k)| + |𝒩₁(x k)| + |𝒩₂(x k)|)
   ≤ |a⁰₀₁(x̄)| + |a⁰₁₀(x̄)| + |a⁻₀₀(x̄)|`.

**Formalization Note.** The proof assumes `a₁₀(x̄) = ∅` without loss of generality; the
statement here keeps the `a₁₀` terms (`|a₁₀(x̄)|` in α and `|a⁰₁₀(x̄)|` on the right). The
nondegeneracy of `x k`, NDC3 and the fixed quadratic index of Theorem 1 are not used. -/
theorem step1_display_14 {n κ : ℕ} (P : MPCC n κ) (t : ℕ → ℝ) (x : ℕ → E n) (μ : ℕ → SMult κ)
    (xbar : E n) (m : MPCCMult κ) (ht : ∀ k, 0 < t k) (ht0 : Tendsto t atTop (𝓝 0))
    (hKKT : ∀ k, P.IsKKT (t k) (x k) (μ k)) (hx : Tendsto x atTop (𝓝 xbar))
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar) (hm : P.StatEq xbar m)
    (hNDC2 : ∀ j ∈ P.a00 xbar, 0 < m.ϱ₁ j * m.ϱ₂ j) :
    ∀ᶠ k in atTop,
      (((P.a01 xbar).card + (P.a10 xbar).card + 2 * (P.a00 xbar).card : ℕ) : ℤ)
          - (((P.H (t k) (x k)).card + (P.N1 (x k)).card + (P.N2 (x k)).card : ℕ) : ℤ)
        ≤ (((P.a01zero xbar m).card + (P.a10zero xbar m).card + (P.a00neg xbar m).card : ℕ) : ℤ) := by sorry

end ScholtesStab
