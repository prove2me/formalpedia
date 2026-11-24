-- Prove2me | Theorems.Thm_OverflowBinPacking_IID_Supplement_theorem_6_2
-- name    : OverflowBinPacking.IID.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:57:58.017096+00:00
-- url     : https://prove2.me/theorems/7a24d685-e18d-491a-94dc-38cb2e0a861c
-- title:
--   Theorem 6.2 (corrected: source-supported accuracy range)
-- statement:
--   Let the independent sizes be supported in $[0,1+\varepsilon]$, with $C\ge1$ and $0<\varepsilon\le(\sqrt{15}-3)/6$. For every deterministic measurable sequential policy $a$ feasible at capacity one, there exists such a policy $b$ for the specified two-step discretized laws satisfying
--   $$\operatorname{cost}_{1+4\varepsilon}(b,\widehat X)\le(1+\varepsilon)\operatorname{cost}_1(a,X).$$
--   The quantifier covers every original feasible policy, including ones that are not optimal. The conversion remains existential and causal; it does not observe the current item before placing it. This is the supported small-accuracy correction of the printed positive-accuracy statement.
--
--   Differences from the source:
--   - encoding: sequential policies and bins → the published zero-based Rule on Fin n, with measurable nonanticipative choices and strict overflow; reason: the immutable model is reused; measurability makes all expectations meaningful and changes no finite-support instance
--   - correction: Theorem 6.2 states no upper epsilon bound → 0 < epsilon <= (sqrt(15)-3)/6; reason: p.24 requires 1/(1-6 epsilon^2)<=1+epsilon; at epsilon=2, n=1, X=1 and C=64, the original cost is 1 but the discretized capacity-9 cost is 5>3; the corrected range excludes this and all other larger accuracies, see DISPROOF.md
--   - encoding: small-outcome randomized coupling and subsequent policy simulation → the precise marginal hatLaw plus existential deterministic policy conversion; reason: fixed simulation randomness may be selected after averaging; no observation of the current realization is supplied to the policy
-- source:
--   Perez-Salazar, Singh & Toriello, Adaptive Bin Packing with Overflow, arXiv:2007.11532v2, p. 21, Theorem 6.2

import Mathlib
import Definitions.Def_OverflowBinPacking_IID_Supplement_Discretization

namespace OverflowBinPacking.IID.Supplement
open MeasureTheory

/-- Corrected accuracy range from the exact inequality on p.24. -/
theorem theorem_6_2 (n : ℕ) (μ : Fin n → Measure ℝ) (C ε : ℝ)
    (hC : 1 ≤ C) (hε : 0 < ε) (hεmax : ε ≤ trackingRange)
    (hμ : BoundedInput μ ε) (a : Rule n) (ha : PolicyAt 1 a) :
    ∃ b : Rule n, PolicyAt (1 + 4 * ε) b ∧
      costAt (fun i => hatLaw (μ i) ε) C (1 + 4 * ε) b ≤
        (1 + ε) * costAt μ C 1 a := by sorry

end OverflowBinPacking.IID.Supplement
