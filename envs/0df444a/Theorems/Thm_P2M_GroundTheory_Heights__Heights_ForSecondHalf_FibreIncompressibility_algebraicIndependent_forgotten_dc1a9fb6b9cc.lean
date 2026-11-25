-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:56.935296+00:00
-- url     : https://prove2.me/theorems/cc842e7f-4be8-4ecf-957e-630fba98056d
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebraic Independent forgotten dc1a9fb6b9cc: P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility al
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebraic Independent forgotten dc1a9fb6b9cc construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Incompressibility algebraic Independent forgotten dc1a9fb6b9cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L62-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreIncompTrdeg.lean#L62-L142

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (V' : Ideal (MRingOver S ι')) [V'.IsPrime] (hV' : IsMultiHomogIdeal V') (i : ∀ k : FibreBlock κ, ι' k.1)
    (hi : ∀ k : FibreBlock κ, (X ⟨k.1, i k⟩ : MRingOver S ι') ∉ V') :
    letI := (Ideal.quotientMap V' (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom le_rfl).toAlgebra
    AlgebraicIndependent (MRingOver S ι ⧸ V'.comap (rename v : MRingOver S ι →ₐ[S] MRingOver S ι').toRingHom)
      (fun k : FibreBlock κ => Ideal.Quotient.mk V' (X ⟨k.1, i k⟩ : MRingOver S ι')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreIncompressibility».«algebraicIndependent_forgotten» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreIncompressibility_algebraicIndependent_forgotten_dc1a9fb6b9cc
