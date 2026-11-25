-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_Dg_indep
-- name    : PositivityTheory.Rg.Sw.LVs.CEq.Dg_indep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:09.583191+00:00
-- url     : https://prove2.me/theorems/6a997694-5371-4947-bc2b-6b9e1697031b
-- title:
--   CEq: Dg indep
-- statement:
--   The CEq construction uses the Dg indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L47-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/CayleyEq.lean#L47-L59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem PositivityTheory.Rg.Sw.LVs.CEq.Dg_indep (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n m : ℕ} (f : κ ≃ Fin n) (g : κ ≃ Fin m) :
    Dg f F = Dg g F := by sorry
