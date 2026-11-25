-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0
-- name    : P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:03:57.49886+00:00
-- url     : https://prove2.me/theorems/07ba267a-6ee9-4c9b-9d88-9956ba6e7827
-- title:
--   P2 M Global Theory LN Cmp O  base Change 149e51dc56c0: P2 M Global Theory LN Cmp O  base Change 149e51dc56c0
-- statement:
--   The P2 M Global Theory LN Cmp O  base Change 149e51dc56c0 construction uses the P2 M Global Theory LN Cmp O  base Change 149e51dc56c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsComparisonCompAlongIdentity.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsComparisonCompAlongIdentity.lean#L22-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsComparisonCompAlongIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.LN GlobalTheory.LN.Cmp

theorem P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0 {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {x' : D'.X} {x : D.X}
    (hc : (D'.c x').left ≫ β = spMap φ ≫ (D.c x).left)
    {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of V))}
    (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left) (hp : p'.left ≫ β = h ≫ p.left) (κ : Fin 4) :
    D'.Oφ p' x' κ ≫ β = h ≫ D.Oφ p x κ := by sorry

alias «GlobalTheory».«LN».«Cmp».«Oφ_baseChange» := P2M_GlobalTheory_LN_Cmp_O__baseChange_149e51dc56c0
