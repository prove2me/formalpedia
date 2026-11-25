-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:41.285076+00:00
-- url     : https://prove2.me/theorems/629e897d-5a45-4830-87e7-666990a06238
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Connected exists ne zero 7c26e2820178: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Connected exists ne zero 7c26e28201
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Connected exists ne zero 7c26e2820178 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Connected exists ne zero 7c26e2820178 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIrreducibleConnected.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PIrreducibleConnected.lean#L10-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StatementsBasicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIrreducibleConnected
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178 {σ : Type} [Fintype σ] {W : Ideal (MvPolynomial σ ℂ)}
    (hW : W.IsPrime) {h : MvPolynomial σ ℂ} (hh : h ∉ W) :
    ∃ x ∈ zeroLocus ℂ W, eval x h ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleConnected».«exists_ne_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleConnected_exists_ne_zero_7c26e2820178
