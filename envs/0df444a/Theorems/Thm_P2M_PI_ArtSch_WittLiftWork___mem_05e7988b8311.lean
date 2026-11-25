-- Prove2me | Theorems.Thm_P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311
-- name    : P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:34.557273+00:00
-- url     : https://prove2.me/theorems/8131558e-aacf-4ea9-9946-cbb0b51ab9a1
-- title:
--   P2 M PI Art Sch Witt Lift Work   mem 05e7988b8311: P2 M PI Art Sch Witt Lift Work   mem 05e7988b8311
-- statement:
--   The P2 M PI Art Sch Witt Lift Work   mem 05e7988b8311 construction uses the P2 M PI Art Sch Witt Lift Work   mem 05e7988b8311 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L100-L105

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

theorem P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311 {n : ℕ} {z : WittVector p k} (hz : z ∈ I n) : δ z ∈ I n := by sorry

alias «PI».«ArtSch».«WittLiftWork».«δ_mem» := P2M_PI_ArtSch_WittLiftWork___mem_05e7988b8311
