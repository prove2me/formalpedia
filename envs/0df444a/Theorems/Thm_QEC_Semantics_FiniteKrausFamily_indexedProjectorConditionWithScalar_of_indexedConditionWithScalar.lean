-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:38:57.984047+00:00
-- url     : https://prove2.me/theorems/aec6708a-015c-418f-a027-4074acd416a1
-- title:
--   Finite Kraus Family: indexed Projector Condition With Scalar of indexed Condition With Scalar
-- statement:
--   The Finite Kraus Family construction uses the indexed Projector Condition With Scalar of indexed Condition With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L101-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L101-L142

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_of_indexedConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by sorry
