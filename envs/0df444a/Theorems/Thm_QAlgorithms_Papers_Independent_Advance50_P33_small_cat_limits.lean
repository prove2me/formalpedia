-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_small_cat_limits
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.small_cat_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:32:56.092576+00:00
-- url     : https://prove2.me/theorems/6f91bf37-b5fe-46cf-9dba-d81fa2aad6df
-- title:
--   Right-hand norm limits of even and odd cats
-- statement:
--   In the full oscillator Hilbert space, let $|c_1(A)\rangle$ and $|c_0(A)\rangle$ be the normalized even and odd superpositions of $|A\rangle$ and $|-A\rangle$. Choose real $A>0$ to fix their optical phase. Then, in Hilbert norm,
--   $$
--   \lim_{A\downarrow0}|c_1(A)\rangle=|0\rangle,\qquad
--   \lim_{A\downarrow0}|c_0(A)\rangle=|1\rangle.
--   $$
--   The limits concern the cat mode alone. No value is assigned to the odd cat at zero, and no direction-independent complex-vector limit is asserted.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 5, III.C: small-amplitude limits of even and odd cats

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5: right-hand norm limits. Positive real amplitudes fix the odd cat's
phase; no complex-direction limit or value of the odd cat at zero is asserted. -/
theorem small_cat_limits :
    CoherentRealized ∧
    Tendsto (fun A : ℝ => cat (A : ℂ) true) (nhdsWithin 0 (Set.Ioi 0)) (nhds (fockKet 0)) ∧
    Tendsto (fun A : ℝ => cat (A : ℂ) false) (nhdsWithin 0 (Set.Ioi 0)) (nhds (fockKet 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
