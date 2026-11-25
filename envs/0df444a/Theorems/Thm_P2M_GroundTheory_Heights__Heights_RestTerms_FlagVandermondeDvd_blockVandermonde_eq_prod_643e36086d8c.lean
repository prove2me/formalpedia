-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:19:55.485538+00:00
-- url     : https://prove2.me/theorems/40c0c8df-508e-4761-bf11-ead079fc0d47
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Vandermonde eq prod 643e36086d8c: P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Vandermonde eq pro
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Vandermonde eq prod 643e36086d8c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Vandermonde eq prod 643e36086d8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeDvd
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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c (f N : ℕ) :
    blockVandermonde f N =
      ∏ t ∈ (univ : Finset (Fin f × Fin N × Fin N)).filter (fun t => t.2.1 < t.2.2),
        ((X (t.1, t.2.1) - X (t.1, t.2.2) : RootRing f N)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagVandermondeDvd».«blockVandermonde_eq_prod» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockVandermonde_eq_prod_643e36086d8c
