-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:29.405109+00:00
-- url     : https://prove2.me/theorems/373dda52-40fb-4ea8-b35c-85a75556a277
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Sign update swap 540d64528759: P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Sign update swap 540d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Sign update swap 540d64528759 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd block Sign update swap 540d64528759 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L41-L47

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759 (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagVandermondeDvd».«blockSign_update_swap» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759
