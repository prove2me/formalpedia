-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
-- name    : QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:59.571201+00:00
-- url     : https://prove2.me/theorems/d95d041b-a8f2-4a60-be00-356eb60dd79d
-- title:
--   Finite Kraus Family: indexed Knill Laflamme Criterion iff indexed Projector Equation
-- statement:
--   The Finite Kraus Family construction uses the indexed Knill Laflamme Criterion iff indexed Projector Equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L188-L198
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L188-L198

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

theorem QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_indexedProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔
      IndexedKnillLaflammeProjectorEquation E C := by sorry
