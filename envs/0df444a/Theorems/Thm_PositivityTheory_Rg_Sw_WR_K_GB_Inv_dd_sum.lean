-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_Inv_dd_sum
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:50:03.358682+00:00
-- url     : https://prove2.me/theorems/6c563d7c-01ca-4592-a9b6-641a13425eb4
-- title:
--   Inv: dd sum
-- statement:
--   The Inv construction uses the dd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBInvar.lean#L50-L57

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv

theorem PositivityTheory.Rg.Sw.WR.K.GB.Inv.dd_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → Mc n → ℂ) (H : Mc n) {x : Mc n}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) :
    dd H (fun y => ∑ i ∈ s, a i * g i y) x = ∑ i ∈ s, a i * dd H (g i) x := by sorry
