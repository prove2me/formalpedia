-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_top_1262eee62470
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_top_1262eee62470
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:12:38.286101+00:00
-- url     : https://prove2.me/theorems/0e76b614-0ca4-479b-8794-7510c3ee7455
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR mult At top 1262eee62470: P2 M Ground Theory Heights  Heights Numbers DVR mult At top 1262eee62470
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR mult At top 1262eee62470 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR mult At top 1262eee62470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L41-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
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
open MvPolynomial
noncomputable section
universe u
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_top_1262eee62470 {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
    (W : Ideal (MRing ι R)) [W.IsPrime] : multAt (⊤ : Ideal (MRing ι R)) W = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«multAt_top» := P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_top_1262eee62470
