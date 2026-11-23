-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b
-- name    : P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:33.817277+00:00
-- url     : https://prove2.me/theorems/543bd0e8-e1bc-496a-ae13-201517986eea
-- title:
--   P2 M Global Theory Level Compat thick Map O  cc5aa398615b: P2 M Global Theory Level Compat thick Map O  cc5aa398615b
-- statement:
--   The P2 M Global Theory Level Compat thick Map O  cc5aa398615b construction uses the P2 M Global Theory Level Compat thick Map O  cc5aa398615b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L37-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.LevelCompat
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g₀ : GtCoord I D e G)
    (g₁ : GtCoord I D (e + 1) G) (hq : thickMap R I e G ≫ g₁.pG.left = g₀.pG.left) (χ : D.X) (k : Fin 4) :
    thickMap R I e G ≫ D.Oφ g₁.pG χ k = D.Oφ g₀.pG χ k := by sorry

alias «GlobalTheory».«LevelCompat».«thickMap_Oφ» := P2M_GlobalTheory_LevelCompat_thickMap_O__cc5aa398615b
