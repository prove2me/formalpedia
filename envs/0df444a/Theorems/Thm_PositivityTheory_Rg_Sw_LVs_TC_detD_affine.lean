-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_detD_affine
-- name    : PositivityTheory.Rg.Sw.LVs.TC.detD_affine
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:05.716962+00:00
-- url     : https://prove2.me/theorems/f67007dd-6a8c-4c90-9dce-37c6da6ea588
-- title:
--   TC: det D affine
-- statement:
--   The TC construction uses the det D affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopComp.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TopComp.lean#L20-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopComp
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
open scoped ContDiff Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.TC.detD_affine (hA : IterAffine) {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω)
    {g : M2 n} (hg : g ∈ Ω) (L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] M2 n) :
    detD (fun t => F (g + L t)) = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => L (single ((Fintype.equivFin (Fin n)).symm i)
        (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) := by sorry
