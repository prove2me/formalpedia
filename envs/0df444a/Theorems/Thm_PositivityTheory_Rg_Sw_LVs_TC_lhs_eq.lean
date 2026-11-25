-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_lhs_eq
-- name    : PositivityTheory.Rg.Sw.LVs.TC.lhs_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:32.265206+00:00
-- url     : https://prove2.me/theorems/42648876-19e7-46e3-a1eb-3f1c99321e41
-- title:
--   TC: lhs eq
-- statement:
--   The TC construction uses the lhs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L45-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCBlock.lean#L45-L108

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

theorem PositivityTheory.Rg.Sw.LVs.TC.lhs_eq (hA : IterAffine) (j : ℕ) (c c' : ℂ) (ψ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (Ω : Set (Matrix (Fin n) (Fin n) ℂ)) (hΩ : IsOpen Ω) (h0 : 0 ∈ Ω) (hψ : ContDiffOn ℂ ∞ ψ Ω) :
    detD (fun t => ψ (bdiag j c c' t)) =
      c ^ (blkA (n := n) j).card * c' ^ (blkB (n := n) j).card *
        ∑ σ : Equiv.Perm (Fin n), if (∀ r, r ∈ blkA (n := n) j ↔ σ r ∈ blkA (n := n) j) then
          (Equiv.Perm.sign σ : ℂ) * iteratedFDeriv ℂ (Fintype.card (Fin n)) ψ 0 (vv σ ∘ (Fintype.equivFin (Fin n)).symm)
          else 0 := by sorry
