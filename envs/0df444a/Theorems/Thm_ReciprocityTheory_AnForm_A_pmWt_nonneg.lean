-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_pmWt_nonneg
-- name    : ReciprocityTheory.AnForm.A.pmWt_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:50.283324+00:00
-- url     : https://prove2.me/theorems/7f37512e-6b20-4e10-9d37-f0ff3b807f23
-- title:
--   A: pm Wt nonneg
-- statement:
--   The A construction uses the pm Wt nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscPos.lean#L59-L60

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

theorem ReciprocityTheory.AnForm.A.pmWt_nonneg (g : Fin D → Fin D × ι) : 0 ≤ pmWt g := by sorry
