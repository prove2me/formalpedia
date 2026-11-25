-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd
-- name    : P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:59.182803+00:00
-- url     : https://prove2.me/theorems/89de2554-291f-42bd-86ef-a400f46a43b9
-- title:
--   P2 M Global Theory ZH Cone Prime eval  cone Hom 6d55f7ae70cd: P2 M Global Theory ZH Cone Prime eval  cone Hom 6d55f7ae70cd
-- statement:
--   The P2 M Global Theory ZH Cone Prime eval  cone Hom 6d55f7ae70cd construction uses the P2 M Global Theory ZH Cone Prime eval  cone Hom 6d55f7ae70cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k J A B : Type} [CommRing k] [CommRing A] [CommRing B]

theorem P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd (c : k →+* A) (r : J → A) (e : A →+* B) (t : B) (f : MvPolynomial J k) :
    Polynomial.eval₂ e t (coneHom c r f) = MvPolynomial.eval₂Hom (e.comp c) (fun j => e (r j) * t) f := by sorry

alias «GlobalTheory».«ZH».«ConePrime».«eval₂_coneHom» := P2M_GlobalTheory_ZH_ConePrime_eval__coneHom_6d55f7ae70cd
