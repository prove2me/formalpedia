-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:33.991617+00:00
-- url     : https://prove2.me/theorems/c2f5f059-efd4-50fb-bd08-f30c084ec05f
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation exists transcendence Basis fin c8a021ddf186: P2 M Ground Theory Heights  Heights Hypersurface Presentation exists transcendence Basis fin
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation exists transcendence Basis fin c8a021ddf186 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation exists transcendence Basis fin c8a021ddf186 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L165-L173

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.HypersurfacePresentation

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186 {S A : Type} [CommRing S] [CommRing A] [IsDomain A] [Algebra S A]
    [FaithfulSMul S A] {ι : Type} [Finite ι] (x : ι → A) (hx : Algebra.adjoin S (Set.range x) = ⊤) :
    ∃ (d : ℕ) (y : Fin d → A), IsTranscendenceBasis S y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«exists_transcendenceBasis_fin» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_exists_transcendenceBasis_fin_c8a021ddf186
