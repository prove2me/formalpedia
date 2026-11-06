-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_sameSpaceKnillLaflammeCriterion
-- name    : QEC.Semantics.FiniteKrausFamily.scale_sameSpaceKnillLaflammeCriterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:33:44.384329+00:00
-- url     : https://prove2.me/theorems/16065f6f-6d99-415b-ab12-9d20d2676ec0
-- title:
--   Finite Kraus Family: scale same Space Knill Laflamme Criterion
-- statement:
--   Same-space KL data is preserved by indexed scalar branch weights.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L281-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L281-L291

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

theorem QEC.Semantics.FiniteKrausFamily.scale_sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (amp : ι → Complex)
    (h : E.sameSpaceKnillLaflammeCriterion C) :
    (E.scale amp).sameSpaceKnillLaflammeCriterion C := by sorry
