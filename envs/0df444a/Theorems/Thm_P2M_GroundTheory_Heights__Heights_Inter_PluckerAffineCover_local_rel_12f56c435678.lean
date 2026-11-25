-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_local_rel_12f56c435678
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_local_rel_12f56c435678
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:21.798854+00:00
-- url     : https://prove2.me/theorems/052b5095-d5b9-4559-9e56-542242292cc5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover local rel 12f56c435678: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover local rel 12f56c435678
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover local rel 12f56c435678 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover local rel 12f56c435678 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L371-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L371-L466

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_local_rel_12f56c435678 (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F) (i : S.ι) :
    ∃ s : Finset (MRing S.YIdx), (∀ r ∈ s, Good S r) ∧
      ∀ w : (Σ k, S.YIdx k) → ℂ, (∀ r ∈ s, eval w (map (Int.castRingHom ℂ) r) = 0) →
        (∀ l k m, eval w (map (Int.castRingHom ℂ) (F i l k m)) = 0) → w ⟨.base, i⟩ = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«local_rel» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_local_rel_12f56c435678
