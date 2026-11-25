-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HodgeTateStep_torsionEnd___041ee141d4de
-- name    : P2M_GlobalTheory_HodgeTateStep_torsionEnd___041ee141d4de
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:24:48.524866+00:00
-- url     : https://prove2.me/theorems/126f340a-da31-4b2c-ac47-642f9d2b33d0
-- title:
--   P2 M Global Theory Hodge Tate Step torsion End   041ee141d4de: P2 M Global Theory Hodge Tate Step torsion End   041ee141d4de
-- statement:
--   The P2 M Global Theory Hodge Tate Step torsion End   041ee141d4de construction uses the P2 M Global Theory Hodge Tate Step torsion End   041ee141d4de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCharactersDlogMinorsGe.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCharactersDlogMinorsGe.lean#L40-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
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
open GlobalTheory
open GlobalTheory.HodgeTateStep
variable {O : Type} [CommRing O]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem P2M_GlobalTheory_HodgeTateStep_torsionEnd___041ee141d4de (a : G ⟶ G) [IsMonHom a] (N : ℕ) :
    torsionEnd a N ≫ torsion.ι G N = torsion.ι G N ≫ a := by sorry

alias «GlobalTheory».«HodgeTateStep».«torsionEnd_ι» := P2M_GlobalTheory_HodgeTateStep_torsionEnd___041ee141d4de
