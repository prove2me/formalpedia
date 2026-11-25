-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BoxDetUnique_gs_zero__4dae196bb222
-- name    : P2M_GlobalTheory_BoxDetUnique_gs_zero__4dae196bb222
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:45.223337+00:00
-- url     : https://prove2.me/theorems/aeec95d6-4b1c-4f6e-91b3-9bed3340e458
-- title:
--   P2 M Global Theory Box Det Unique gs zero  4dae196bb222: P2 M Global Theory Box Det Unique gs zero  4dae196bb222
-- statement:
--   The P2 M Global Theory Box Det Unique gs zero  4dae196bb222 construction uses the P2 M Global Theory Box Det Unique gs zero  4dae196bb222 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsBoxSec.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsBoxSec.lean#L37-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CardHomVanishingOfDiagBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetKroneckerPower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
variable {X Y Z : Scheme.{0}} {R : Type} [CommRing R]

theorem P2M_GlobalTheory_BoxDetUnique_gs_zero__4dae196bb222 (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by sorry

alias «GlobalTheory».«BoxDetUnique».«gs_zero'» := P2M_GlobalTheory_BoxDetUnique_gs_zero__4dae196bb222
