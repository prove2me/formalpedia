-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:24.625432+00:00
-- url     : https://prove2.me/theorems/e1be4a73-2224-56e8-bc8b-950572e11516
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top eq mstar of 205773e62c79: P2 M Ground Theory Heights  Heights Rest Terms Top eq mstar of 205773e62c79
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top eq mstar of 205773e62c79 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top eq mstar of 205773e62c79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L77-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L77-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79 (f r a : ℕ) (q : Fin f → ℕ) (e : ℕ) (τ : Fin f) (m : Fin f → ℕ)
    (hm : m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e)
    (h : ∀ σ, σ ≠ τ → m σ = r * a - q σ) : m = mstar f r a q e τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«eq_mstar_of» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_eq_mstar_of_205773e62c79
