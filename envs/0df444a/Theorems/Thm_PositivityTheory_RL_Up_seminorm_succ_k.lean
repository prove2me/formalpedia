-- Prove2me | Theorems.Thm_PositivityTheory_RL_Up_seminorm_succ_k
-- name    : PositivityTheory.RL.Up.seminorm_succ_k
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:52.129464+00:00
-- url     : https://prove2.me/theorems/4c36ed78-7583-4ae2-a07b-78aa0bc7c890
-- title:
--   Up: seminorm succ k
-- statement:
--   The Up construction uses the seminorm succ k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L175-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/RLLieA.lean#L175-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]

theorem PositivityTheory.RL.Up.seminorm_succ_k (k : ℕ) (g : Sch l) :
    SchwartzMap.seminorm ℂ (k + 1) 0 g ≤ ∑ i, SchwartzMap.seminorm ℂ k 0 (dRho (Pi.single (Sum.inr i) 1) g) := by sorry
