-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_pullU_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.res_pullU_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:32.928584+00:00
-- url     : https://prove2.me/theorems/1a13d4f4-2efa-4149-8b06-bdcd217636e8
-- title:
--   DVR: res pull U eq
-- statement:
--   The DVR construction uses the res pull U eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocal.lean#L28-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.DVR.res_pullU_eq {X Y : Scheme.{0}} (f : Y ⟶ X) {U W : X.Opens} (h : W ≤ U) {Z : Y.Opens}
    (hZ : Z ≤ f ⁻¹ᵁ U) (hZ' : Z ≤ f ⁻¹ᵁ W) (x : Γ(X, U)ˣ) :
    res hZ (pullU f U x) = res hZ' (pullU f W (res h x)) := by sorry
