-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_sub_mem_of_coeff_eq
-- name    : PI.ArtSch.WittLiftWork.sub_mem_of_coeff_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:43.272198+00:00
-- url     : https://prove2.me/theorems/92ac9037-ab19-4c1c-8da5-6668a3f14fd2
-- title:
--   Witt Lift Work: sub mem of coeff eq
-- statement:
--   The Witt Lift Work construction uses the sub mem of coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L38-L42

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

theorem PI.ArtSch.WittLiftWork.sub_mem_of_coeff_eq {n : ℕ} {a b : WittVector p k} (h : ∀ i < n, a.coeff i = b.coeff i) :
    a - b ∈ I n := by sorry
