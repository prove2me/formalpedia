-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P13_operation_holevo_lower_semicontinuity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P13.operation_holevo_lower_semicontinuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:42:00.044418+00:00
-- url     : https://prove2.me/theorems/d14d4594-d621-4ee4-bfdb-d6c64c5c14ad
-- title:
--   Section 6 unnumbered operation lower semicontinuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one, channels are complex-linear completely positive trace-preserving maps on the full trace class, and all logarithms are natural. For any fixed generalized input ensemble $\mu$, on the full space of completely positive trace-nonincreasing operations with pointwise output trace-norm topology,
--
--   $$\Phi\longmapsto\chi_\Phi(\mu)\quad\text{is lower semicontinuous}.$$
--
--   This allows approximation by trace-decreasing operations without assuming finite entropy.
-- source:
--   On the entanglement-assisted classical capacity of infinite-dimensional quantum channels, arXiv:1210.6926v2, PDF p. 21, Section 6 unnumbered operation lower semicontinuity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P13

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

namespace QAlgorithms.Papers.Independent.Claimed50.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- TraceDecreasingOperation lower semicontinuity, PDF p.21: trace-decreasing operations and
arbitrary measures; no pure-support or finite-entropy premise is needed. -/
theorem operation_holevo_lower_semicontinuity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (mu : Ens.GeneralizedEnsemble I) :
    LowerSemicontinuous (fun Phi : TraceDecreasingOperation I J => Ens.ensembleHolevo Phi.val mu) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P13

end
