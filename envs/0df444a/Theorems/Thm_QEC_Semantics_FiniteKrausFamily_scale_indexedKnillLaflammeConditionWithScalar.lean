-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_indexedKnillLaflammeConditionWithScalar
-- name    : QEC.Semantics.FiniteKrausFamily.scale_indexedKnillLaflammeConditionWithScalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:42:40.917781+00:00
-- url     : https://prove2.me/theorems/00ea645c-ce52-4d6e-8acd-8a016b0d9249
-- title:
--   Finite Kraus Family: scale indexed Knill Laflamme Condition With Scalar
-- statement:
--   Indexed KL scalar data is preserved by indexed scalar branch weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L76-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L76-L84

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

theorem QEC.Semantics.FiniteKrausFamily.scale_indexedKnillLaflammeConditionWithScalar
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (amp : ι → Complex) {scalar : ι → ι → Complex}
    (h : IndexedKnillLaflammeConditionWithScalar E C scalar) :
    IndexedKnillLaflammeConditionWithScalar (E.scale amp) C
      (fun i j => star (amp i) * amp j * scalar i j) := by sorry
