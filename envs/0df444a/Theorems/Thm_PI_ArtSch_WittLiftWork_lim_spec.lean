-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_lim_spec
-- name    : PI.ArtSch.WittLiftWork.lim_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:12.303819+00:00
-- url     : https://prove2.me/theorems/555b49ed-3cb5-4311-bb4b-06c2f926003e
-- title:
--   Witt Lift Work: lim spec
-- statement:
--   The Witt Lift Work construction uses the lim spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L193-L206

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittCoefficients_CoeffEqOfSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.WittLiftWork
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k]
variable [CharP k p]
variable (hAS : ∀ a : k, ∃ y : k, y ^ p - y = a)
include hAS

theorem PI.ArtSch.WittLiftWork.lim_spec (x : WittVector p k) : δ (lim hAS x) = x := by sorry
