-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_complete_diagonal_sum
-- name    : QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_complete_diagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:43:13.239572+00:00
-- url     : https://prove2.me/theorems/2cd44836-4b13-41f4-9c60-056ce011e1d0
-- title:
--   Finite Kraus Family: indexed Projector Condition With Scalar complete diagonal sum
-- statement:
--   For complete finite Kraus noise, indexed KL projector data has normalized
--   diagonal scalar sum on the code projector.
--
--   This is the scalar-normalization step needed before building a CPTP recovery
--   from the KL Gram data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L35-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L35-L61

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

theorem QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_complete_diagonal_sum
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector := by sorry
