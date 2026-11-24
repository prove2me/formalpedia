-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_an_eval
-- name    : PositivityTheory.Rg.Sw.WR.Z.an_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:19.893384+00:00
-- url     : https://prove2.me/theorems/32965a4e-99ef-464b-9345-104f1f3132cd
-- title:
--   Z: an eval
-- statement:
--   The Z construction uses the an eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L170-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L170-L179

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Z.an_eval {ι : Type} (f : ι → MC n → ℂ) (B₀ : MC n) (hf : ∀ k, AnalyticAt ℂ (f k) B₀)
    (R : MvPolynomial ι ℂ) : AnalyticAt ℂ (fun B => MvPolynomial.eval (fun k => f k B) R) B₀ := by sorry
