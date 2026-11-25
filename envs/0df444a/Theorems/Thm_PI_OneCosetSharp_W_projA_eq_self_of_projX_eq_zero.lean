-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_projA_eq_self_of_projX_eq_zero
-- name    : PI.OneCosetSharp.W.projA_eq_self_of_projX_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:06.111291+00:00
-- url     : https://prove2.me/theorems/8f219fac-c02e-4d55-8e48-aadae32802ca
-- title:
--   W: proj A eq self of proj X eq zero
-- statement:
--   The W construction uses the proj A eq self of proj X eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/GaStep.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/GaStep.lean#L28-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_GaStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}

theorem PI.OneCosetSharp.W.projA_eq_self_of_projX_eq_zero {w : Fin (n + c) → k} (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : AP w = w := by sorry
