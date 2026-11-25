-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_dirC
-- name    : PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_dirC
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:19.608817+00:00
-- url     : https://prove2.me/theorems/489fde67-3fec-4ac1-be42-66ad526d20ec
-- title:
--   TW: cont Diff dir C
-- statement:
--   The TW construction uses the cont Diff dir C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GBTwist.lean#L52-L56

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_dirC {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : Fin n → Fin n → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => dirC f w y) := by sorry
