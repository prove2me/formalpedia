-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:55.359001+00:00
-- url     : https://prove2.me/theorems/d42695e1-5e6b-5380-9179-c6e6332e466f
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility coeff eval  scale c1644af1f8da: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility coeff eval  scal
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility coeff eval  scale c1644af1f8da construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility coeff eval  scale c1644af1f8da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L33-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L33-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreIncompTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreIncompressibility
variable {S : Type} [CommRing S]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da {σ R A : Type} [Fintype σ] [CommRing R] [CommRing A] (f : R →+* A) (b : σ → A)
    (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (eval₂ ((C : A →+* MvPolynomial σ A).comp f) (fun k => X k * C (b k)) P) =
      f (coeff m P) * ∏ k, b k ^ m k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«coeff_eval₂_scale» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_coeff_eval__scale_c1644af1f8da
