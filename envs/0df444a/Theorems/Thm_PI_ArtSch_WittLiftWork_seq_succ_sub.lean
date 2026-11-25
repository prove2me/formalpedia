-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_seq_succ_sub
-- name    : PI.ArtSch.WittLiftWork.seq_succ_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:55.874731+00:00
-- url     : https://prove2.me/theorems/eeaa8232-fd5a-4b7a-841a-3177e8baa2d5
-- title:
--   Witt Lift Work: seq succ sub
-- statement:
--   The Witt Lift Work construction uses the seq succ sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L160-L165

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

theorem PI.ArtSch.WittLiftWork.seq_succ_sub (x : WittVector p k) (n : ℕ) :
    (seq hAS x (n + 1)).1 - (seq hAS x n).1 ∈ I n := by sorry
