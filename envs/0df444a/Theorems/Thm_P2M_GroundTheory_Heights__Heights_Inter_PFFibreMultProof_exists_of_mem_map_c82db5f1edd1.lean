-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:33.171856+00:00
-- url     : https://prove2.me/theorems/95cdba05-7289-4a7d-88b1-b23a90bd96b0
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists of mem map c82db5f1edd1: P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists of mem map c82db5f1edd1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists of mem map c82db5f1edd1 construction uses the P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof exists of mem map c82db5f1edd1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L113-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L113-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFFibreMultProof
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
omit [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1 (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι'))
    {g : MRingOver G.Φ (fibreIdx ι' κ)} (hg : g ∈ W.map (baseSubst κ G)) :
    ∃ (t : MRing ι) (w : MRing ι'), aeval G.x t ≠ 0 ∧ w ∈ W ∧
      baseSubst κ G (rename v t) * g = baseSubst κ G w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFFibreMultProof».«exists_of_mem_map» := P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_exists_of_mem_map_c82db5f1edd1
