-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eval__scale_of_isHomogeneous_ea2ff51b767f
-- name    : P2M_GlobalTheory_eval__scale_of_isHomogeneous_ea2ff51b767f
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:12:31.646538+00:00
-- url     : https://prove2.me/theorems/f1baa54c-085c-4fbd-8565-6ac37552bf2a
-- title:
--   P2 M Global Theory eval  scale of is Homogeneous ea2ff51b767f: P2 M Global Theory eval  scale of is Homogeneous ea2ff51b767f
-- statement:
--   The P2 M Global Theory eval  scale of is Homogeneous ea2ff51b767f construction uses the P2 M Global Theory eval  scale of is Homogeneous ea2ff51b767f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DehomogenisationIsRadicalAndTorsionFree.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DehomogenisationIsRadicalAndTorsionFree.lean#L13-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DehomogenisationIsRadicalAndTorsionFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem P2M_GlobalTheory_eval__scale_of_isHomogeneous_ea2ff51b767f {o σ S : Type} [CommRing o] [CommRing S] (f : o →+* S)
    (g : σ → S) (u : S) {F : MvPolynomial σ o} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ f (fun j => g j * u) F = MvPolynomial.eval₂ f g F * u ^ e := by sorry

alias «GlobalTheory».«eval₂_scale_of_isHomogeneous» := P2M_GlobalTheory_eval__scale_of_isHomogeneous_ea2ff51b767f
