-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rhs_eq
-- name    : PositivityTheory.Rg.Sw.LVs.TC.rhs_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:01.773794+00:00
-- url     : https://prove2.me/theorems/23d27597-08fe-5b29-bfd0-fb6aa0bb4fc8
-- title:
--   TC: rhs eq
-- statement:
--   The TC construction uses the rhs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L174-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L174-L219

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

theorem PositivityTheory.Rg.Sw.LVs.TC.rhs_eq (hA : IterAffine) (hS : IterSymm) (hN : IterNested) (j : ℕ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
      ψ (embOn (blkA j) T + embOn (blkB j) S))) =
    ∑ σA : Equiv.Perm (blkA (n := n) j), ∑ τ : Equiv.Perm (blkB (n := n) j),
      (Equiv.Perm.sign σA : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv (piP j σA τ) ∘ (Fintype.equivFin (Fin n)).symm) := by sorry
