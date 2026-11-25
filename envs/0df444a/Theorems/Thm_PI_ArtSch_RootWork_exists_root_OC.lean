-- Prove2me | Theorems.Thm_PI_ArtSch_RootWork_exists_root_OC
-- name    : PI.ArtSch.RootWork.exists_root_OC
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:40.320602+00:00
-- url     : https://prove2.me/theorems/f05a6190-5e4c-4fe2-8e4b-5f35d06528ce
-- title:
--   Root Work: exists root OC
-- statement:
--   The Root Work construction uses the exists root OC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArtinSchreierRoots/ExistsRootOC.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArtinSchreierRoots/ExistsRootOC.lean#L10-L39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArtinSchreierRoots_ExistsRootOC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.RootWork
open Polynomial
variable (l : ℕ) [Fact l.Prime]

theorem PI.ArtSch.RootWork.exists_root_OC (c b : OC l) : ∃ z : OC l, z ^ l - c * z - b = 0 := by sorry
