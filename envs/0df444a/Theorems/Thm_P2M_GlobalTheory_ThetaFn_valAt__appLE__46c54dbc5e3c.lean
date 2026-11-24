-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c
-- name    : P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:21:51.590943+00:00
-- url     : https://prove2.me/theorems/8b1e41a8-d565-4f70-8e32-0c3efbe7e40b
-- title:
--   P2 M Global Theory Theta Fn val At  app LE  46c54dbc5e3c: P2 M Global Theory Theta Fn val At  app LE  46c54dbc5e3c
-- statement:
--   The P2 M Global Theory Theta Fn val At  app LE  46c54dbc5e3c construction uses the P2 M Global Theory Theta Fn val At  app LE  46c54dbc5e3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L57-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c (φ : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, U)) :
    valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by sorry

alias «GlobalTheory».«ThetaFn».«valAt'_appLE'» := P2M_GlobalTheory_ThetaFn_valAt__appLE__46c54dbc5e3c
