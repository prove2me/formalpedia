-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:07.989304+00:00
-- url     : https://prove2.me/theorems/b7222728-85bc-482d-b91e-c6ce411c3bda
-- title:
--   P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof comap fibre Of and is Prime e91ae4bf3f4e: P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof comap fibre Of and is Prime e91ae4bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof comap fibre Of and is Prime e91ae4bf3f4e construction uses the P2 M Ground Theory Heights  Heights Inter PFFibre Mult Proof comap fibre Of and is Prime e91ae4bf3f4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L138-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreMult.lean#L138-L173

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e (hv : IsBlockMap κ v) (G : GenFibre v P') (W : Ideal (MRing ι')) [W.IsPrime]
    (hPW : P' ≤ W) (hI : imageZ v W = imageZ v P') :
    (fibreOf κ G W).comap (baseSubst κ G) = W ∧ (fibreOf κ G W).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PFFibreMultProof».«comap_fibreOf_and_isPrime» := P2M_GroundTheory_Heights__Heights_Inter_PFFibreMultProof_comap_fibreOf_and_isPrime_e91ae4bf3f4e
