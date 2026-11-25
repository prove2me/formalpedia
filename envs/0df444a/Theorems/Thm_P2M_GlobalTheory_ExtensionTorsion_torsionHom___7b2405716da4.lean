-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4
-- name    : P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:26:44.731921+00:00
-- url     : https://prove2.me/theorems/b1d55d63-8fa2-502b-9c53-e9898802e0b1
-- title:
--   P2 M Global Theory Extension Torsion torsion Hom   7b2405716da4: P2 M Global Theory Extension Torsion torsion Hom   7b2405716da4
-- statement:
--   The P2 M Global Theory Extension Torsion torsion Hom   7b2405716da4 construction uses the P2 M Global Theory Extension Torsion torsion Hom   7b2405716da4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsFiniteFlatTorsionOfIsGt.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsFiniteFlatTorsionOfIsGt.lean#L26-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsFiniteFlatTorsionOfIsGt
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
open GlobalTheory.ExtensionTorsion
open KernelNoTorsion
variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4 (q : G ⟶ B) [IsMonHom q] (N : ℕ) :
    torsionHom q N ≫ torsion.ι B N = torsion.ι G N ≫ q := by sorry

alias «GlobalTheory».«ExtensionTorsion».«torsionHom_ι» := P2M_GlobalTheory_ExtensionTorsion_torsionHom___7b2405716da4
