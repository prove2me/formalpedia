-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_imageZ_comap_8783b4fe6943
-- name    : P2M_GroundTheory_Heights__Heights_Inter_imageZ_comap_8783b4fe6943
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:45.229181+00:00
-- url     : https://prove2.me/theorems/49f1a6f4-8723-5709-ac97-4994930b2d07
-- title:
--   P2 M Ground Theory Heights  Heights Inter image Z comap 8783b4fe6943: P2 M Ground Theory Heights  Heights Inter image Z comap 8783b4fe6943
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter image Z comap 8783b4fe6943 construction uses the P2 M Ground Theory Heights  Heights Inter image Z comap 8783b4fe6943 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L138-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFFibreBij.lean#L138-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreBij
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

theorem P2M_GroundTheory_Heights__Heights_Inter_imageZ_comap_8783b4fe6943 (hv : IsBlockMap κ v) (G : GenFibre v P') {Q : Ideal (MRingOver G.Φ (fibreIdx ι' κ))}
    (hQ : Q ≠ ⊤) : imageZ v (Q.comap (baseSubst κ G)) = imageZ v P' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«imageZ_comap» := P2M_GroundTheory_Heights__Heights_Inter_imageZ_comap_8783b4fe6943
