-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_add___822b92b3e7e3
-- name    : P2M_ReciprocityTheory_AnForm_M_add___822b92b3e7e3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:57.650253+00:00
-- url     : https://prove2.me/theorems/95f2fdeb-71e4-4989-b1d9-55a828576d66
-- title:
--   P2 M Reciprocity Theory An Form M add   822b92b3e7e3: P2 M Reciprocity Theory An Form M add   822b92b3e7e3
-- statement:
--   The P2 M Reciprocity Theory An Form M add   822b92b3e7e3 construction uses the P2 M Reciprocity Theory An Form M add   822b92b3e7e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffAtOfIsPotential.lean#L31-L31

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_ReciprocityTheory_AnForm_M_add___822b92b3e7e3 (P Q : LocPot X) (x : X) : (P + Q).φ x = fun y => P.φ x y + Q.φ x y := by sorry

alias «ReciprocityTheory».«AnForm».«M».«add_φ» := P2M_ReciprocityTheory_AnForm_M_add___822b92b3e7e3
