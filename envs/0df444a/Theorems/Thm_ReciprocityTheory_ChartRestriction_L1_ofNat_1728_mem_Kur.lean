-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ofNat_1728_mem_Kur
-- name    : ReciprocityTheory.ChartRestriction.L1.ofNat_1728_mem_Kur
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:58:29.858616+00:00
-- url     : https://prove2.me/theorems/b0d0c12b-db75-5665-89d4-5a4aa8be3e59
-- title:
--   L1: of Nat 1728 mem Kur
-- statement:
--   The L1 construction uses the of Nat 1728 mem Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedModel.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedModel.lean#L39-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedKur
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedModel
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
variable (l : ℕ) [Fact l.Prime]

theorem ReciprocityTheory.ChartRestriction.L1.ofNat_1728_mem_Kur : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by sorry
