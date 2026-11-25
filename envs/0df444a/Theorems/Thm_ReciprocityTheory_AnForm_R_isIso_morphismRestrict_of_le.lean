-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isIso_morphismRestrict_of_le
-- name    : ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:08:39.390799+00:00
-- url     : https://prove2.me/theorems/bca4a2b3-8d8c-4b4f-91f3-04a0b49b5079
-- title:
--   R: is Iso morphism Restrict of le
-- statement:
--   The R construction uses the is Iso morphism Restrict of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsC.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsC.lean#L43-L52

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by sorry
