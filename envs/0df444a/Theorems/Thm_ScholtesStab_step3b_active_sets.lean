-- Prove2me | Theorems.Thm_ScholtesStab_step3b_active_sets
-- name    : ScholtesStab.step3b_active_sets
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:37.416827+00:00
-- url     : https://prove2.me/theorems/96d41e7a-067e-40b1-9233-32824d426b26
-- title:
--   Proof of Theorem 1, Step 3b: identification of $\mathcal H(x^t)$, $\mathcal N_1(x^t)$, $\mathcal N_2(x^t)$
-- statement:
--   In the setting of display (14) (KKT points $x^k\to\bar x\in M$ of $\mathcal S$ with $t_k\downarrow0$, MPCC-LICQ at $\bar x$, multipliers $(\bar\sigma,\bar\varrho)$ with (5) and NDC2), for all sufficiently large $k$:
--
--   $$
--   \begin{aligned}
--   \mathcal H(x^k)&=a^-_{01}(\bar x)\cup a^-_{10}(\bar x)\cup a^-_{00}(\bar x)\cup\bigl((a^0_{01}(\bar x)\cup a^0_{10}(\bar x))\cap\mathcal H(x^k)\bigr),\\
--   \mathcal N_1(x^k)&=a^+_{01}(\bar x)\cup a^+_{00}(\bar x)\cup\bigl(a^0_{01}(\bar x)\cap\mathcal N_1(x^k)\bigr),\\
--   \mathcal N_2(x^k)&=a^+_{10}(\bar x)\cup a^+_{00}(\bar x)\cup\bigl(a^0_{10}(\bar x)\cap\mathcal N_2(x^k)\bigr).
--   \end{aligned}
--   $$
--
--   Only the indices whose multiplier vanishes are undetermined by the signs at the limit.
--
--   Differences from the source:
--   - encoding: ℝⁿ, indices j = 1, …, κ → EuclideanSpace ℝ (Fin n), indices in Fin κ (0-based); reason: a relabelling of coordinates and indices; same instances
--   - encoding: f, F₁, F₂ twice continuously differentiable (standing assumption, p.1) → ContDiff ℝ 2 fields of the structure MPCC; reason: the standing assumption is carried by every instance; same instances
--   - encoding: differentials DF(x), Hessians D²L(x) → fderiv ℝ F x : ℝⁿ →L[ℝ] ℝ and fderiv ℝ (fderiv ℝ L) x as a bilinear form; reason: the Fréchet derivative of a C² function is its differential and its second derivative is the Hessian; linear independence of differentials is that of gradients
--   - encoding: multipliers σ̄₁,ⱼ (j ∈ a₀₁), σ̄₂,ⱼ (j ∈ a₁₀), ϱ̄₁,ⱼ, ϱ̄₂,ⱼ (j ∈ a₀₀) → total functions Fin κ → ℝ whose values outside these index sets are never used; reason: every formula and count ranges over the paper's index sets only; same instances
--   - encoding: a sequence xᵗ converging to x̄ for t → 0 ("for all sufficiently small t", "for infinitely many t") → t : ℕ → ℝ with t k > 0 and t k → 0, x k → x̄; ∀ᶠ k in atTop and ∃ᶠ k in atTop; reason: the standard sequential reading of the paper's sequence; t k > 0 because S is defined for t > 0
--   - generalization: ℋ(xᵗ) = a⁻₀₁ ∪ a⁻₀₀ ∪ (a⁰₀₁ ∩ ℋ(xᵗ)), 𝒩₁(xᵗ) = a⁺₀₁ ∪ a⁺₀₀ ∪ (a⁰₀₁ ∩ 𝒩₁(xᵗ)), 𝒩₂(xᵗ) = a⁺₀₀ under the proof's assumption a₁₀(x̄) = ∅ (p.18, "without loss of generality") → the general statement with the a₁₀ terms; reason: setting a₁₀(x̄) = ∅ makes the a₁₀ terms vanish and gives the printed claim
--   - generalization: the setting of Theorem 1 (nondegenerate KKT points of quadratic index q, x̄ nondegenerate C-stationary) → KKT points (not necessarily nondegenerate), MPCC-LICQ at x̄, and multipliers with (5) and NDC2; reason: the hypotheses of Theorem 1 imply these, so the statement specializes to the printed claim
-- source:
--   Lämmel & Shikhman, On stability of the Scholtes regularization for mathematical programs with complementarity constraints, arXiv:2501.07383v2, Proof of Theorem 1, Step 3b, p.20

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

/-- **Identification of the active index sets of S near x̄.** Lämmel–Shikhman,
arXiv:2501.07383v2, Proof of Theorem 1, Step 3b, p.20: "By continuity arguments, we get
a₀₁(x̄) ∩ 𝒩₂(xᵗ) = ∅ for all t sufficiently small. By combining this with Corollary 1, NDC2, and
a₁₀(x̄) = ∅, we have for all t sufficiently small:
ℋ(xᵗ) = a⁻₀₁(x̄) ∪ a⁻₀₀(x̄) ∪ (a⁰₀₁(x̄) ∩ ℋ(xᵗ)),
𝒩₁(xᵗ) = a⁺₀₁(x̄) ∪ a⁺₀₀(x̄) ∪ (a⁰₀₁(x̄) ∩ 𝒩₁(xᵗ)),   𝒩₂(xᵗ) = a⁺₀₀(x̄)."

In the setting of `step1_display_14`, for all sufficiently large `k`:
`ℋ(x k) = a⁻₀₁ ∪ a⁻₁₀ ∪ a⁻₀₀ ∪ ((a⁰₀₁ ∪ a⁰₁₀) ∩ ℋ(x k))`,
`𝒩₁(x k) = a⁺₀₁ ∪ a⁺₀₀ ∪ (a⁰₀₁ ∩ 𝒩₁(x k))`,
`𝒩₂(x k) = a⁺₁₀ ∪ a⁺₀₀ ∪ (a⁰₁₀ ∩ 𝒩₂(x k))` (index sets at `x̄` with multipliers `(σ̄, ϱ̄)`).

**Formalization Note.** The page assumes `a₁₀(x̄) = ∅` without loss of generality; the
statement keeps the `a₁₀` terms and reduces to the printed display when `a₁₀(x̄) = ∅`. The
inclusion (18) that the page derives next is not part of this statement. -/
theorem step3b_active_sets {n κ : ℕ} (P : MPCC n κ) (t : ℕ → ℝ) (x : ℕ → E n)
    (μ : ℕ → SMult κ) (xbar : E n) (m : MPCCMult κ) (ht : ∀ k, 0 < t k)
    (ht0 : Tendsto t atTop (𝓝 0))
    (hKKT : ∀ k, P.IsKKT (t k) (x k) (μ k)) (hx : Tendsto x atTop (𝓝 xbar))
    (hxbar : xbar ∈ P.M) (hLICQ : P.MPCCLICQ xbar) (hm : P.StatEq xbar m)
    (hNDC2 : ∀ j ∈ P.a00 xbar, 0 < m.ϱ₁ j * m.ϱ₂ j) :
    ∀ᶠ k in atTop,
      P.H (t k) (x k) = P.a01neg xbar m ∪ P.a10neg xbar m ∪ P.a00neg xbar m ∪
          ((P.a01zero xbar m ∪ P.a10zero xbar m) ∩ P.H (t k) (x k)) ∧
      P.N1 (x k) = P.a01pos xbar m ∪ P.a00pos xbar m ∪ (P.a01zero xbar m ∩ P.N1 (x k)) ∧
      P.N2 (x k) = P.a10pos xbar m ∪ P.a00pos xbar m ∪ (P.a10zero xbar m ∩ P.N2 (x k)) := by sorry

end ScholtesStab
