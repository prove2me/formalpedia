-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_cpart_sum
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.cpart_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:26.365781+00:00
-- url     : https://prove2.me/theorems/99763b0a-1475-4645-b47f-9898b3c9a954
-- title:
--   GB: cpart sum
-- statement:
--   The GB construction uses the cpart sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L146-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBLink.lean#L146-L159

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}

theorem PositivityTheory.Rg.Sw.WR.K.GB.cpart_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by sorry
