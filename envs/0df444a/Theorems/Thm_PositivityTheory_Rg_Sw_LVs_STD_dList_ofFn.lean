-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dList_ofFn
-- name    : PositivityTheory.Rg.Sw.LVs.STD.dList_ofFn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:15.26649+00:00
-- url     : https://prove2.me/theorems/57188bdc-9b38-4cfa-a697-26648d95c011
-- title:
--   STD: d List of Fn
-- statement:
--   The STD construction uses the d List of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffC.lean#L29-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffC.lean#L29-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.STD.dList_ofFn {r : ℝ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hG : ContDiffOn ℂ ∞ G (Metric.ball 0 r)) :
    ∀ (k : ℕ) (m : Fin k → Fin n × Fin n) (x : Vr n), herm x ∈ Metric.ball 0 r →
      dList (List.ofFn m) (fun y => G (herm y)) x =
        iteratedFDeriv ℂ k G (herm x) (fun i => Matrix.single (m i).1 (m i).2 1)
  := by sorry
