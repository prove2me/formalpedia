-- Prove2me | Theorems.Thm_PI_LatMinWork_norm_two_eq_one
-- name    : PI.LatMinWork.norm_two_eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:33:46.244356+00:00
-- url     : https://prove2.me/theorems/962146ce-3b97-56b3-a902-7b793a036806
-- title:
--   Lat Min Work: norm two eq one
-- statement:
--   The Lat Min Work construction uses the norm two eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinimalLatticeNorm/NormTwoEqOne.lean#L8-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]

theorem PI.LatMinWork.norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by sorry
