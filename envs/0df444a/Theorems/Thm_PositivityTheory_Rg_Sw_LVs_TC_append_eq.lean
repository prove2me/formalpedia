-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_append_eq
-- name    : PositivityTheory.Rg.Sw.LVs.TC.append_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:51.106991+00:00
-- url     : https://prove2.me/theorems/54fe04b3-280d-4b07-9b37-ba784e28c1e8
-- title:
--   TC: append eq
-- statement:
--   The TC construction uses the append eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L110-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L110-L149

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.TC.append_eq (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) :
    Fin.append (fun i => embL (blkA (n := n) j) (single ((Fintype.equivFin (blkA (n := n) j)).symm i)
        (σA ((Fintype.equivFin (blkA (n := n) j)).symm i)) (1 : ℂ)))
      (fun i => embL (blkB (n := n) j) (single ((Fintype.equivFin (blkB (n := n) j)).symm i)
        (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) (1 : ℂ))) = vv (piP j σA τ) ∘ epsE j := by sorry
