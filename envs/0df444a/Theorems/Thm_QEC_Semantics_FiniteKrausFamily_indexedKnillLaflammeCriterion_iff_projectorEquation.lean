-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_projectorEquation
-- name    : QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_projectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:57.202989+00:00
-- url     : https://prove2.me/theorems/4b26b018-2515-4ed1-b437-00b7a17cb982
-- title:
--   Finite Kraus Family: indexed Knill Laflamme Criterion iff projector Equation
-- statement:
--   The indexed finite-Kraus KL criterion matches the projector-equation form over
--   the same finite-Kraus error set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L318-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L318-L323

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

theorem QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_projectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔
      KnillLaflammeProjectorEquation C E.sameSpaceErrorSet := by sorry
