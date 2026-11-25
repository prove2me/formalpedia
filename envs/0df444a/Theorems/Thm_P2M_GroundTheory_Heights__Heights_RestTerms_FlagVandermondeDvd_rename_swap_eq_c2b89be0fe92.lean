-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:59.348256+00:00
-- url     : https://prove2.me/theorems/fb75c6b7-b2b1-4858-808b-f51f97f466bf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd rename swap eq c2b89be0fe92: P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd rename swap eq c2b89be0fe92
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd rename swap eq c2b89be0fe92 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Vandermonde Dvd rename swap eq c2b89be0fe92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagVandermondeDvd.lean#L27-L39

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92 (f N : ℕ) (τ : Fin f) (i j : Fin N) :
    (rename (Equiv.swap (τ, i) (τ, j)) : RootRing f N →ₐ[ℚ] RootRing f N) =
      blockPermute f N (Function.update 1 τ (Equiv.swap i j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagVandermondeDvd».«rename_swap_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_rename_swap_eq_c2b89be0fe92
