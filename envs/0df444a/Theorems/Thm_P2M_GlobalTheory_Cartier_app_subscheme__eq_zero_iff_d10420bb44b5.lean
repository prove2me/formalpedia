-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5
-- name    : P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:41.867674+00:00
-- url     : https://prove2.me/theorems/cbe70ada-16c4-4add-a2dc-db40b3787fdd
-- title:
--   P2 M Global Theory Cartier app subscheme  eq zero iff d10420bb44b5: P2 M Global Theory Cartier app subscheme  eq zero iff d10420bb44b5
-- statement:
--   The P2 M Global Theory Cartier app subscheme  eq zero iff d10420bb44b5 construction uses the P2 M Global Theory Cartier app subscheme  eq zero iff d10420bb44b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L562-L577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L562-L577

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}

theorem P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5 (J : Y.IdealSheafData) {V : Y.Opens} (b : Γ(Y, V)) :
    (J.subschemeι.app V).hom b = 0 ↔
      ∀ (W : Y.affineOpens) (h : W.1 ≤ V), resG Y h b ∈ J.ideal W := by sorry

alias «GlobalTheory».«Cartier».«app_subschemeι_eq_zero_iff» := P2M_GlobalTheory_Cartier_app_subscheme__eq_zero_iff_d10420bb44b5
