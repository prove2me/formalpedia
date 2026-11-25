-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_sqD_normSq
-- name    : ReciprocityTheory.ChartRestriction.L1.sqD_normSq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:36.86349+00:00
-- url     : https://prove2.me/theorems/e803d71e-65ec-519f-b1e7-0aacf9efa781
-- title:
--   L1: sq D norm Sq
-- statement:
--   The L1 construction uses the sq D norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedKerPrin.lean#L17-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPoly
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HasCMByStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKerPrin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.sqD_normSq (d r : ℕ) : Complex.normSq ((r : ℂ) + redSqD d) = ((r ^ 2 + d : ℕ) : ℝ) := by sorry
