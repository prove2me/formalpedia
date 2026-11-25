-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:44.078207+00:00
-- url     : https://prove2.me/theorems/fe45bf82-90ea-4a0f-9cb2-61045bec4fe4
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line prod line pow 7d765d194025: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line prod line pow 7d765d194025
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line prod line pow 7d765d194025 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line prod line pow 7d765d194025 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L33-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
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
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025 (a c : K → ℚ) (s : K → ℕ) (S : Finset K) :
    (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ ∑ k ∈ S, s k ∧
      (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).coeff (∑ k ∈ S, s k) = ∏ k ∈ S, a k ^ (s k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«prod_line_pow» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_prod_line_pow_7d765d194025
