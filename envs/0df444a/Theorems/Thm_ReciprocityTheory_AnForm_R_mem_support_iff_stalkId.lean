-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mem_support_iff_stalkId
-- name    : ReciprocityTheory.AnForm.R.mem_support_iff_stalkId
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:58.370313+00:00
-- url     : https://prove2.me/theorems/a84d5ff8-fa88-4e7f-96a1-3c39debe3999
-- title:
--   R: mem support iff stalk Id
-- statement:
--   The R construction uses the mem support iff stalk Id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L158-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L158-L180

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
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
universe u

theorem ReciprocityTheory.AnForm.R.mem_support_iff_stalkId {W : Scheme.{0}} (G : W.IdealSheafData) (x : W) :
    x ∈ (G.support : Set W) ↔ FinalTheorems.stalkId G x ≠ ⊤ := by sorry
