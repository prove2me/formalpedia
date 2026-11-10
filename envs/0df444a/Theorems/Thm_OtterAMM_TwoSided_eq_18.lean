-- Prove2me | Theorems.Thm_OtterAMM_TwoSided_eq_18
-- name    : OtterAMM.TwoSided.eq_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:47:04.908986+00:00
-- url     : https://prove2.me/theorems/950559f7-922d-40ca-9a0f-080c6b901477
-- title:
--   §5, Eq. (18) — layer-cake formula $W_F(S)=\int_0^{\sigma_0}\min\{D_S(t),K_F(t)\}\,dt$
-- statement:
--   Let $G$ be a one-sided compensation curve with $\sigma_0=G'_+(0)$, and $S$ a finite set of sell-Y bids with asks $\tilde v_i\ge0$ and budgets $\tilde q_i\ge0$. With $D_S(t)=\sum_{i\in S}\tilde q_i\mathbf 1\{\tilde v_i\le t\}$ and $K_G(t)=\sup\{y\ge0:G'_+(y)\ge t\}$ (possibly $+\infty$), the function $t\mapsto\min\{D_S(t),K_G(t)\}$ is integrable on $[0,\sigma_0]$ and
--   $$W_G(S)=\int_0^{\sigma_0}\min\{D_S(t),K_G(t)\}\,dt.\qquad(18)$$
--   It yields the submodularity of Theorem 16(d) and is the tool of Lemma 17.
--
--   Differences from the source:
--   - encoding: K_F(t) with the supremum allowed to be +∞ → thresholdQty in EReal; the integrand min{D_S(t), K(t)} is taken in EReal and converted to ℝ (it is finite); reason: D_S(t) is finite, so the minimum is a real number
--   - encoding: the integral of (18) → a conjunct asserting IntervalIntegrable of the integrand on [0, σ0] precedes the equality; reason: Lean's integral of a non-integrable function is 0; the conjunct makes the equality the printed one (the integrand is bounded and measurable, so this is implicit in the paper)
--   - encoding: F′₊(y) → rightDeriv G y = derivWithin G (Ici y) y; reason: the right derivative of a concave function exists on [0, ∞) here
--   - encoding: W_F(S) = max over the box 0 ≤ y_i ≤ q̃_i (Eq. (3)) → W = sSup of the welfare over the box; reason: for a one-sided curve the welfare is continuous on a compact nonempty box, so the supremum is the attained maximum
--   - encoding: identities, the block and its reports → identities are labels in ℕ, a block is a Finset of labels with a report function rep (an ordered block is a List of labels); reason: a finite set of identities with reports is exactly such a pair; labels are never compared by the mechanism except through the selection rule
--   - encoding: F : [0, +∞) → ℝ≥0 a one-sided curve (§3.1) → G : ℝ → ℝ with IsOneSidedCurve G, every condition imposed on [0, +∞); σ0 = slope0 G = derivWithin G (Ici 0) 0; reason: values off [0, +∞) are never used
--   - encoding: asks ṽ_i ≥ 0 and budgets q̃_i ≥ 0 (§3.1) → hypothesis haq: 0 ≤ a i ∧ 0 ≤ q i for i ∈ S; reason: the paper's domain of reports, not an extra condition
-- source:
--   Shi, Zhang, Chung, Li, Otter: A Provably MEV-Resilient Automated Market Maker via Surplus Redistribution, arXiv:2609.03474 (held copy sha256 3a05f18a…), pp. 19–20, §5, Eq. (18) (PDF 21–22)

import Mathlib
import Definitions.Def_OtterAMM_TwoSided_Curve
import Definitions.Def_OtterAMM_TwoSided_Model
import Definitions.Def_OtterAMM_TwoSided_VCG

set_option autoImplicit false

namespace OtterAMM.TwoSided

/-- §5, Eq. (18) (pp. 19–20): the layer-cake formula `W_G(S) = ∫_0^{σ0} min{D_S(t), K_G(t)} dt`
for a one-sided curve `G` with `σ0 = G'₊(0)` (the integrand is integrable). -/
theorem eq_18 (G : ℝ → ℝ) (hG : IsOneSidedCurve G) (S : Finset Ident) (a q : Ident → ℝ)
    (haq : ∀ i ∈ S, 0 ≤ a i ∧ 0 ≤ q i) :
    IntervalIntegrable (layer G S a q) MeasureTheory.volume 0 (slope0 G) ∧
      W G S a q = ∫ t in (0 : ℝ)..(slope0 G), layer G S a q t := by sorry

end OtterAMM.TwoSided
