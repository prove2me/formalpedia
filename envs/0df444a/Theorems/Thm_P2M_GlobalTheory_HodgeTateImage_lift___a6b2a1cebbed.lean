-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HodgeTateImage_lift___a6b2a1cebbed
-- name    : P2M_GlobalTheory_HodgeTateImage_lift___a6b2a1cebbed
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:42.545941+00:00
-- url     : https://prove2.me/theorems/1e0bd6d0-9615-4ddc-be5b-cdc66f65eb90
-- title:
--   P2 M Global Theory Hodge Tate Image lift   a6b2a1cebbed: P2 M Global Theory Hodge Tate Image lift   a6b2a1cebbed
-- statement:
--   The P2 M Global Theory Hodge Tate Image lift   a6b2a1cebbed construction uses the P2 M Global Theory Hodge Tate Image lift   a6b2a1cebbed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueIsAl.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueIsAl.lean#L60-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HodgeTateImage
open GlobalTheory.TangentPow GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}

theorem P2M_GlobalTheory_HodgeTateImage_lift___a6b2a1cebbed {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : lift hR x ≫ torsion.ι G (p ^ n) = bc R x := by sorry

alias «GlobalTheory».«HodgeTateImage».«lift_ι» := P2M_GlobalTheory_HodgeTateImage_lift___a6b2a1cebbed
