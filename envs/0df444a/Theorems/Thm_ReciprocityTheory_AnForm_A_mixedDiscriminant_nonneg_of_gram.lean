-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mixedDiscriminant_nonneg_of_gram
-- name    : ReciprocityTheory.AnForm.A.mixedDiscriminant_nonneg_of_gram
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:27.789358+00:00
-- url     : https://prove2.me/theorems/accc07f2-9114-4b86-81b8-cdf693420324
-- title:
--   A: mixed Discriminant nonneg of gram
-- statement:
--   The A construction uses the mixed Discriminant nonneg of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L166-L172

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Finset
open scoped ComplexOrder
variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.AnForm.A.mixedDiscriminant_nonneg_of_gram (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (hA : ∀ k, (A k).PosSemidef) : (mdisc A).im = 0 ∧ 0 ≤ (mdisc A).re := by sorry
