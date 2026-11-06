-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_iff_indexedProjectorConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_iff_indexedProjectorConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:35.135832+00:00
-- url     : https://prove2.me/theorems/a9e8a942-f6f6-4003-9f7f-6e11cafdb50c
-- title:
--   Finite Kraus Family: indexed Condition With Scalar iff indexed Projector Condition With Scalar
-- statement:
--   The Finite Kraus Family construction uses the indexed Condition With Scalar iff indexed Projector Condition With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L179-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L179-L186

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

theorem QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_iff_indexedProjectorConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (scalar : ι → ι → Complex) :
    IndexedKnillLaflammeConditionWithScalar E C scalar ↔
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar := by sorry
