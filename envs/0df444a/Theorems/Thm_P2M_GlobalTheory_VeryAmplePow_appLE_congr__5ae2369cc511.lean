-- Prove2me | Theorems.Thm_P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511
-- name    : P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:14.489671+00:00
-- url     : https://prove2.me/theorems/4379e040-c026-48ea-8574-1bcc439b5577
-- title:
--   P2 M Global Theory Very Ample Pow app LE congr  5ae2369cc511: P2 M Global Theory Very Ample Pow app LE congr  5ae2369cc511
-- statement:
--   The P2 M Global Theory Very Ample Pow app LE congr  5ae2369cc511 construction uses the P2 M Global Theory Very Ample Pow app LE congr  5ae2369cc511 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L19-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511 {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (e : g = g') {U : Y.Opens} {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V h = g'.appLE U V (e ▸ h) := by sorry

alias «GlobalTheory».«VeryAmplePow».«appLE_congr'» := P2M_GlobalTheory_VeryAmplePow_appLE_congr__5ae2369cc511
