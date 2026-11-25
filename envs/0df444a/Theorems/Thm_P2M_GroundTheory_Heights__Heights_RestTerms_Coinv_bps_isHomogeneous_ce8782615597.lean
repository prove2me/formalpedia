-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_isHomogeneous_ce8782615597
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_isHomogeneous_ce8782615597
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:18:37.369876+00:00
-- url     : https://prove2.me/theorems/a4e82afe-45e1-4523-b138-9cceec04a54a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv bps is Homogeneous ce8782615597: P2 M Ground Theory Heights  Heights Rest Terms Coinv bps is Homogeneous ce8782615597
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv bps is Homogeneous ce8782615597 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv bps is Homogeneous ce8782615597 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvIdealComponent.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PCoinvIdealComponent.lean#L11-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_isHomogeneous_ce8782615597 (K : Type) [Field K] (f n m : ℕ) (b : Fin f) :
    (bps K f n m b).IsHomogeneous m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«bps_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_isHomogeneous_ce8782615597
