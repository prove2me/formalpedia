-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_projectorEquation
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_projectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:12:14.556703+00:00
-- url     : https://prove2.me/theorems/c7df286e-a0a0-4348-a977-0d1202a6e958
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion iff projector Equation
-- statement:
--   The same-space finite-Kraus KL criterion matches the projector-equation form
--   over the same finite-Kraus error set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L308-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L308-L312

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

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_projectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      KnillLaflammeProjectorEquation C E.sameSpaceErrorSet := by sorry
