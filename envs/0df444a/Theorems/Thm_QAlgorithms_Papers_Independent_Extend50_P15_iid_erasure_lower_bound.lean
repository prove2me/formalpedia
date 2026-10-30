-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P15_iid_erasure_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P15.iid_erasure_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:57:03.524738+00:00
-- url     : https://prove2.me/theorems/22c1d568-2570-4115-b3c9-50e979c39a1d
-- title:
--   Independent erasure lower bound for all covariant codes
-- statement:
--   Fix $d\ge2$, $n\ge1$, and $p_e\in(0,1/2)$. Consider any CPTP encoder of one logical $d$-level system into $n$ physical $d$-level systems, exactly covariant under the defining $\mathrm{SU}(d)$ action with a fixed gate-or-identity transversal action. Allow any CPTP decoder on the full flagged output tensor space. If every physical site is erased independently with probability $p_e$, then
--
--   $$\epsilon_{\mathrm{cov}}\ge\frac{p_e}{64n(1-p_e)}.$$
--
--   The error is the maximum over logical gates of half the diamond distance from the ideal logical channel, including arbitrary entangled reference inputs. This bounds all covariant codes in the source's i.i.d. erasure regime.
-- source:
--   Optimal Universal Quantum Error Correction via Bounded Reference Frames, arXiv:2007.09154v2, PDF p. 26, Proposition 2, C17

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P15

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P15

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P75 (Register)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Proposition 2, C17, PDF pp.6,26. Retains C1's range p∈(0,1/2) and n≥1. -/
theorem iid_erasure_lower_bound (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (p : ℝ) (hp : 0 < p) (hpHalf : p < 1 / 2) (code : CovariantCode d n) :
    p / (64 * n * (1 - p)) ≤ covariantError code (iidErasure d n p) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P15

end
