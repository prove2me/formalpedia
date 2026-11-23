-- Prove2me | Theorems.Thm_PI_ArtSch_WittLiftWork_coeff_eq_of_sub_mem
-- name    : PI.ArtSch.WittLiftWork.coeff_eq_of_sub_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:49.8479+00:00
-- url     : https://prove2.me/theorems/38da1674-fbbc-4de2-ad8c-7a38a0555222
-- title:
--   Witt Lift Work: coeff eq of sub mem
-- statement:
--   The Witt Lift Work construction uses the coeff eq of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittCoefficients/CoeffEqOfSubMem.lean#L31-L36

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

theorem PI.ArtSch.WittLiftWork.coeff_eq_of_sub_mem {n : ℕ} {a b : WittVector p k} (hab : a - b ∈ I n) {i : ℕ} (hi : i < n) :
    a.coeff i = b.coeff i := by sorry
