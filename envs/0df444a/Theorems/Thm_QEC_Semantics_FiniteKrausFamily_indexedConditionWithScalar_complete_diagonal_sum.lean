-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_complete_diagonal_sum
-- name    : QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_complete_diagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:14:57.269859+00:00
-- url     : https://prove2.me/theorems/fb0dd263-0d18-4db0-a25c-b2966031197b
-- title:
--   Finite Kraus Family: indexed Condition With Scalar complete diagonal sum
-- statement:
--   The matrix-element indexed KL scalar data for a complete family has normalized
--   diagonal scalar sum on the code projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L105-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L105-L112

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_complete_diagonal_sum
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector := by sorry
