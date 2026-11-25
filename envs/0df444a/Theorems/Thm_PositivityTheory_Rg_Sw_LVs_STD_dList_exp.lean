-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_dList_exp
-- name    : PositivityTheory.Rg.Sw.LVs.STD.dList_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:27.134702+00:00
-- url     : https://prove2.me/theorems/6dbd2c9a-5e18-47f7-ba6c-a53a8f79967f
-- title:
--   STD: d List exp
-- statement:
--   The STD construction uses the d List exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean#L33-L50

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
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

theorem PositivityTheory.Rg.Sw.LVs.STD.dList_exp (β : Matrix (Fin n) (Fin n) ℂ) :
    ∀ (l : List (Fin n × Fin n)) (c : ℂ) (x : Vr n),
      dList l (fun y => c * Complex.exp (ell β (herm y))) x =
        c * (l.map fun a => ell β (Matrix.single a.1 a.2 1)).prod * Complex.exp (ell β (herm x))
  := by sorry
