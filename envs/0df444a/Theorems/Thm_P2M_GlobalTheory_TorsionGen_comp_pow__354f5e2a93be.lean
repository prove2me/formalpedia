-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TorsionGen_comp_pow__354f5e2a93be
-- name    : P2M_GlobalTheory_TorsionGen_comp_pow__354f5e2a93be
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:54:55.300731+00:00
-- url     : https://prove2.me/theorems/4b61d33f-730c-4cfb-be74-3724195ad83d
-- title:
--   P2 M Global Theory Torsion Gen comp pow  354f5e2a93be: P2 M Global Theory Torsion Gen comp pow  354f5e2a93be
-- statement:
--   The P2 M Global Theory Torsion Gen comp pow  354f5e2a93be construction uses the P2 M Global Theory Torsion Gen comp pow  354f5e2a93be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdCocycleMul.lean#L151-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdCocycleMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionGen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
omit [IsCommMonObj G]

theorem P2M_GlobalTheory_TorsionGen_comp_pow__354f5e2a93be {T T' : Over S} (ρ : T' ⟶ T) (a : T ⟶ G) (k : ℕ) : ρ ≫ a ^ k = (ρ ≫ a) ^ k := by sorry

alias «GlobalTheory».«TorsionGen».«comp_pow'» := P2M_GlobalTheory_TorsionGen_comp_pow__354f5e2a93be
