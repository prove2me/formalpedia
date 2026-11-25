-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:58.993054+00:00
-- url     : https://prove2.me/theorems/3022fb74-842b-4dbd-a137-7973a704b2c7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mem map aeval ef7f27c20847: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke I
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mem map aeval ef7f27c20847 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter weighted Homogeneous Component mem map aeval ef7f27c20847 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogGrad.lean#L42-L54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847 [DecidableEq M] {w : σ → M} {ω : τ → M}
    {e : σ → MvPolynomial τ R} (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v))
    (G : Set (MvPolynomial σ R)) (hG : ∀ f ∈ G, ∃ a, IsWeightedHomogeneous w f a)
    {f : MvPolynomial τ R} (hf : f ∈ Ideal.map (aeval e) (Ideal.span G)) (m : M) :
    weightedHomogeneousComponent ω m f ∈ Ideal.map (aeval e) (Ideal.span G) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«weightedHomogeneousComponent_mem_map_aeval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mem_map_aeval_ef7f27c20847
