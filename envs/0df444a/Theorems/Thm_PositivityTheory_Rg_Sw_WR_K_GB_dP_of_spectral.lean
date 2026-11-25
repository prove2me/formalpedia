-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_dP_of_spectral
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.dP_of_spectral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:09:06.385737+00:00
-- url     : https://prove2.me/theorems/96c03754-9220-5be0-bbf2-c809bb2d6969
-- title:
--   GB: d P of spectral
-- statement:
--   The GB construction uses the d P of spectral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L97-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBFinal.lean#L97-L114

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBFinal
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

theorem PositivityTheory.Rg.Sw.WR.K.GB.dP_of_spectral (y : E n) (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (lam : Fin n → ℝ)
    (hy : herm y = k * Matrix.diagonal (fun i => (lam i : ℂ)) * kᴴ) : dP y = ∏ i, (1 + lam i ^ 2) := by sorry
