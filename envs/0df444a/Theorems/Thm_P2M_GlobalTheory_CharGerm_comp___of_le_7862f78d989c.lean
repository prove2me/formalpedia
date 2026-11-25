-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CharGerm_comp___of_le_7862f78d989c
-- name    : P2M_GlobalTheory_CharGerm_comp___of_le_7862f78d989c
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:57:19.170302+00:00
-- url     : https://prove2.me/theorems/eacfe3da-8bbc-5f88-ad4e-5439c041570b
-- title:
--   P2 M Global Theory Char Germ comp   of le 7862f78d989c: P2 M Global Theory Char Germ comp   of le 7862f78d989c
-- statement:
--   The P2 M Global Theory Char Germ comp   of le 7862f78d989c construction uses the P2 M Global Theory Char Germ comp   of le 7862f78d989c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfTorsionCharacters.lean#L321-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSeriesOfTorsionCharacters.lean#L321-L331

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
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
open GlobalTheory
open GlobalTheory.CharGerm
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.KernelNoTorsion GlobalTheory.GmPoints
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {p : ℕ}
  (χ : Tv G p)

theorem P2M_GlobalTheory_CharGerm_comp___of_le_7862f78d989c {T : Over (Spec (CommRingCat.of R₀))} {m n : ℕ} (h : m ≤ n)
    (u : T ⟶ torsion G (p ^ m)) (v : T ⟶ torsion G (p ^ n))
    (huv : u ≫ torsion.ι G (p ^ m) = v ≫ torsion.ι G (p ^ n)) : u ≫ χ.χ m = v ≫ χ.χ n := by sorry

alias «GlobalTheory».«CharGerm».«comp_χ_of_le» := P2M_GlobalTheory_CharGerm_comp___of_le_7862f78d989c
