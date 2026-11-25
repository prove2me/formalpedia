-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorsionIntegral_gt__comp_44a8eff960f5
-- name    : P2M_GlobalTheory_TorsionIntegral_gt__comp_44a8eff960f5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:56.593644+00:00
-- url     : https://prove2.me/theorems/142539c8-7e29-4ccf-8232-5dbdbf8d94ff
-- title:
--   P2 M Global Theory Torsion Integral gt  comp 44a8eff960f5: P2 M Global Theory Torsion Integral gt  comp 44a8eff960f5
-- statement:
--   The P2 M Global Theory Torsion Integral gt  comp 44a8eff960f5 construction uses the P2 M Global Theory Torsion Integral gt  comp 44a8eff960f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L240-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorsionPointsIntegral.lean#L240-L246

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (z : (TF (R := R) F).left)

theorem P2M_GlobalTheory_TorsionIntegral_gt__comp_44a8eff960f5 {b' : T ⟶ D.P.A} {b : TF (R := R) F ⟶ D.P.A} (hb : φ ≫ b' = b) (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F b χ k = φ.left ≫ DegPre.gtφT D T b' χ k := by sorry

alias «GlobalTheory».«TorsionIntegral».«gtφ_comp» := P2M_GlobalTheory_TorsionIntegral_gt__comp_44a8eff960f5
