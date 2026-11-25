-- Prove2me | Theorems.Thm_P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83
-- name    : P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:21.652805+00:00
-- url     : https://prove2.me/theorems/d9378fa9-2445-402b-8492-95856409dc51
-- title:
--   P2 M Global Theory WCub tri th  d2b9dc26ad83: P2 M Global Theory WCub tri th  d2b9dc26ad83
-- statement:
--   The P2 M Global Theory WCub tri th  d2b9dc26ad83 construction uses the P2 M Global Theory WCub tri th  d2b9dc26ad83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L61-L74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
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
noncomputable section
open GlobalTheory
open GlobalTheory.WCub
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))

theorem P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83 [GrpObj G] [IsCommMonObj G] [GrpObj E] [IsCommMonObj E] (q : E ⟶ (Over.pullback f).obj G)
    [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst G.hom f) (k : thK) :
    tri f p x ≫ thφ G (x3 G) k = (psum E x k.down).left ≫ p.left := by sorry

alias «GlobalTheory».«WCub».«tri_thφ» := P2M_GlobalTheory_WCub_tri_th__d2b9dc26ad83
