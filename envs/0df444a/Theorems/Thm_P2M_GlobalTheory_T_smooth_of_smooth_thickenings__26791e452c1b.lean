-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_smooth_of_smooth_thickenings__26791e452c1b
-- name    : P2M_GlobalTheory_T_smooth_of_smooth_thickenings__26791e452c1b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:55:37.446843+00:00
-- url     : https://prove2.me/theorems/91af93c0-78db-5cf1-a86f-5ea3bc3581b4
-- title:
--   P2 M Global Theory T smooth of smooth thickenings  26791e452c1b: P2 M Global Theory T smooth of smooth thickenings  26791e452c1b
-- statement:
--   The P2 M Global Theory T smooth of smooth thickenings  26791e452c1b construction uses the P2 M Global Theory T smooth of smooth thickenings  26791e452c1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmoothOfSmoothThickeningsStatement.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SmoothOfSmoothThickeningsStatement.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothOfSmoothThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothOfSmoothThickeningsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_smooth_of_smooth_thickenings__26791e452c1b : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by sorry

alias «GlobalTheory».«T».«smooth_of_smooth_thickenings'» := P2M_GlobalTheory_T_smooth_of_smooth_thickenings__26791e452c1b
