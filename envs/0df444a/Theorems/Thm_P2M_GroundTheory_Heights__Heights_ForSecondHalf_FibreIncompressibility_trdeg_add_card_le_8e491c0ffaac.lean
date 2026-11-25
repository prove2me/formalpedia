-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_trdeg_add_card_le_8e491c0ffaac
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_trdeg_add_card_le_8e491c0ffaac
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:49.97292+00:00
-- url     : https://prove2.me/theorems/62e0d3e8-246d-43d4-aa40-b47aa6125ab8
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility trdeg add card le 8e491c0ffaac: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility trdeg add card l
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility trdeg add card le 8e491c0ffaac construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility trdeg add card le 8e491c0ffaac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L146-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L146-L171

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
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_trdeg_add_card_le_8e491c0ffaac [Nontrivial S] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (hrel : IsRelevant V')
    (hinj : Function.Injective (algebraMap S
      (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom))) :
    Algebra.trdeg S (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom) +
        Fintype.card (FibreBlock κ) ≤ Algebra.trdeg S (MRingOver S ι' ⧸ V') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«trdeg_add_card_le» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_trdeg_add_card_le_8e491c0ffaac
