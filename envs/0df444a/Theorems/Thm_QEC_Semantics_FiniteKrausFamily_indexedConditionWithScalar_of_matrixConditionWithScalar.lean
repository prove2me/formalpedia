-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedConditionWithScalar_of_matrixConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_of_matrixConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:12:16.040479+00:00
-- url     : https://prove2.me/theorems/28f99eee-96d9-4b92-b2ed-f984b0796793
-- title:
--   Finite Kraus Family: indexed Condition With Scalar of matrix Condition With Scalar
-- statement:
--   The Finite Kraus Family construction uses the indexed Condition With Scalar of matrix Condition With Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L213-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L213-L220

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

theorem QEC.Semantics.FiniteKrausFamily.indexedConditionWithScalar_of_matrixConditionWithScalar
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : Operator H → Operator H → Complex}
    (h : KnillLaflammeMatrixConditionWithScalar C E.sameSpaceErrorSet scalar) :
    IndexedKnillLaflammeConditionWithScalar E C
      (fun i j => scalar (E.operator i) (E.operator j)) := by sorry
