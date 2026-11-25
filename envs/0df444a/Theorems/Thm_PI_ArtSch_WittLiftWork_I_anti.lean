-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_I_anti
-- name    : PI.ArtSch.WittLiftWork.I_anti
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:44.655405+00:00
-- url     : https://prove2.me/theorems/b7f4a212-4541-563d-ab98-f1fdb4fc75b2
-- title:
--   Witt Lift Work: I anti
-- statement:
--   The Witt Lift Work construction uses the I anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L25-L26

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

theorem PI.ArtSch.WittLiftWork.I_anti {m n : ℕ} (h : n ≤ m) {x : WittVector p k} (hx : x ∈ I m) : x ∈ I n := by sorry
