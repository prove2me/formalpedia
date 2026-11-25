-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_foldr_fderiv_eq
-- name    : PositivityTheory.Rg.Sw.WR.Z.foldr_fderiv_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:55.869627+00:00
-- url     : https://prove2.me/theorems/12b8cce1-9410-52be-927a-4d18239e107c
-- title:
--   Z: foldr fderiv eq
-- statement:
--   The Z construction uses the foldr fderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L262-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L262-L288

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

theorem PositivityTheory.Rg.Sw.WR.Z.foldr_fderiv_eq (G : MC n → ℂ) (U : Set (MC n)) (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) :
    ∀ (m : ℕ) (v : Fin m → MC n),
      AnalyticOnNhd ℂ ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) U ∧
      ∀ B ∈ U, ((List.finRange m).foldr (fun k H => fun B => fderiv ℂ H B (v k)) G) B = iteratedFDeriv ℂ m G B v := by sorry
