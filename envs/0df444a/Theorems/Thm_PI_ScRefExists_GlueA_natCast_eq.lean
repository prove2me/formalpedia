-- Prove2me | Theorems.Thm_PI_ScRefExists_GlueA_natCast_eq
-- name    : PI.ScRefExists.GlueA.natCast_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:25:09.684263+00:00
-- url     : https://prove2.me/theorems/a1e67dc5-f4f3-5878-9fab-9bb9aef47f05
-- title:
--   Glue A: nat Cast eq
-- statement:
--   The Glue A construction uses the nat Cast eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeReferenceFrame/HANegRight.lean#L67-L68

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GlueA
variable (I : Formalism.MainNotions.S.AutInst)

theorem PI.ScRefExists.GlueA.natCast_eq (m : ℕ) : (m : (I.E ⊗[I.F] Af I.F)) = Formalism.UG.inclE (F := I.F) (Af I.F) (m : I.E) := by sorry
