-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_long_625589269fc3
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_long_625589269fc3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:29.193506+00:00
-- url     : https://prove2.me/theorems/4a1c9c97-3a65-57f3-8616-54bb18633f9b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff long 625589269fc3: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff long 625589269fc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff long 625589269fc3 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Polynomial list Diff long 625589269fc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolynomial.lean#L39-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolynomial
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Finset fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial
variable {K : Type} [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_long_625589269fc3 {n : ℕ} {g : (K → ℕ) → ℚ}
    (hg : ∀ L : List K, L.length = n + 1 → listDiff L g = 0) (L : List K) (hL : n + 1 ≤ L.length) :
    listDiff L g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolynomial».«listDiff_long» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolynomial_listDiff_long_625589269fc3
