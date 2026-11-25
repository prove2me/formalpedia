-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d
-- name    : P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:16.725503+00:00
-- url     : https://prove2.me/theorems/ae5e4134-0140-4da2-92a9-c0a8459903e0
-- title:
--   P2 M Ground Theory Heights  Heights MCLog Det Gram Deriv key bound 462b1424da6d: P2 M Ground Theory Heights  Heights MCLog Det Gram Deriv key bound 462b1424da6d
-- statement:
--   The P2 M Ground Theory Heights  Heights MCLog Det Gram Deriv key bound 462b1424da6d construction uses the P2 M Ground Theory Heights  Heights MCLog Det Gram Deriv key bound 462b1424da6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramDeriv.lean#L19-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/PLogDetGramDeriv.lean#L19-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCLogDetGramDeriv

theorem P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d (g k : ℕ) (a b x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) :
    (k.factorial : ℝ) * k * ((g : ℝ) ^ 2 * a ^ 2 * x) ^ (k - 1) *
        ((g : ℝ) ^ 2 * (2 * a ^ 2 * x + a ^ 2 * ((g : ℝ) ^ 2 * x ^ 2 * b))) ≤
      constK g k * (1 + a) ^ (2 * k) * (1 + x) ^ (k + 1) * (1 + b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MCLogDetGramDeriv».«key_bound» := P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d
