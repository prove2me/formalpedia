-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0
-- name    : P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:48.907845+00:00
-- url     : https://prove2.me/theorems/629ba454-a343-4b22-9b38-05afed921d47
-- title:
--   P2 M Global Theory Ab Law Pow Vanish pre inf  f58b070a9db0: P2 M Global Theory Ab Law Pow Vanish pre inf  f58b070a9db0
-- statement:
--   The P2 M Global Theory Ab Law Pow Vanish pre inf  f58b070a9db0 construction uses the P2 M Global Theory Ab Law Pow Vanish pre inf  f58b070a9db0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesDescent.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesDescent.lean#L26-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
variable {X Y Z : Scheme.{0}}

theorem P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0 (h : Y ⟶ X) (U U' : X.Opens) : h ⁻¹ᵁ (U ⊓ U') ≤ h ⁻¹ᵁ U ⊓ h ⁻¹ᵁ U' := by sorry

alias «GlobalTheory».«AbLaw».«PowVanish».«pre_inf'» := P2M_GlobalTheory_AbLaw_PowVanish_pre_inf__f58b070a9db0
