-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_map_coneMap_c5f542395ec3
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_map_coneMap_c5f542395ec3
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:11:58.25723+00:00
-- url     : https://prove2.me/theorems/fdd786ce-7687-441c-94fc-4de4e3d5f25c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR map cone Map c5f542395ec3: P2 M Ground Theory Heights  Heights Numbers DVR map cone Map c5f542395ec3
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR map cone Map c5f542395ec3 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR map cone Map c5f542395ec3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L36-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_map_coneMap_c5f542395ec3 {σ τ R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] (f : R →+* B)
    (g : B →+* B') (c : σ → B) (q : σ → τ) (x : MvPolynomial σ R) :
    map g (eval₂ (C.comp f) (fun p => C (c p) * X (q p)) x) =
      eval₂ (C.comp (g.comp f)) (fun p => C (g (c p)) * X (q p)) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«map_coneMap» := P2M_GroundTheory_Heights__Heights_NumbersDVR_map_coneMap_c5f542395ec3
