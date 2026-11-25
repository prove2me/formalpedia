-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_foldr_Dkl
-- name    : PositivityTheory.Rg.Sw.WR.Z.foldr_Dkl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:03:21.595071+00:00
-- url     : https://prove2.me/theorems/8cfd2ffe-2316-4ea0-a2fa-278367f19d41
-- title:
--   Z: foldr Dkl
-- statement:
--   The Z construction uses the foldr Dkl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L290-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsGainA.lean#L290-L306

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

theorem PositivityTheory.Rg.Sw.WR.Z.foldr_Dkl (σ : Equiv.Perm (Fin n)) (U : Set (MC n)) (hU : IsOpen U) (hherm : ∀ y : E n, (herm y : MC n) ∈ U)
    (G : MC n → ℂ) (hG : AnalyticOnNhd ℂ G U) :
    ∀ L : List (Fin n), AnalyticOnNhd ℂ (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) U ∧
      L.foldr (fun k g => Dkl k (σ k) g) (fun y => G (herm y)) =
        fun y => (L.foldr (fun k H => fun B => fderiv ℂ H B (eU (σ k) k)) G) (herm y) := by sorry
