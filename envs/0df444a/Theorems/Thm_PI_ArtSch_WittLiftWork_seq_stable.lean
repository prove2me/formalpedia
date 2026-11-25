-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_seq_stable
-- name    : PI.ArtSch.WittLiftWork.seq_stable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:57.365332+00:00
-- url     : https://prove2.me/theorems/ddb21940-600e-450f-a2f1-2b762999268b
-- title:
--   Witt Lift Work: seq stable
-- statement:
--   The Witt Lift Work construction uses the seq stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L167-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L167-L183

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

theorem PI.ArtSch.WittLiftWork.seq_stable (x : WittVector p k) (n : ℕ) :
    ∀ m, n ≤ m → (seq hAS x m).1 - (seq hAS x n).1 ∈ I n := by sorry
