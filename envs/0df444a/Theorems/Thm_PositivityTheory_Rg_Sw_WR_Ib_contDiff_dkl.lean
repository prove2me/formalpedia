-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_contDiff_dkl
-- name    : PositivityTheory.Rg.Sw.WR.Ib.contDiff_dkl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:39.767248+00:00
-- url     : https://prove2.me/theorems/a7c80cdb-2270-4a6c-982b-98c02ac88d95
-- title:
--   Ib: cont Diff dkl
-- statement:
--   The Ib construction uses the cont Diff dkl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L118-L122

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.Ib.contDiff_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k l : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (Dkl k l g) := by sorry
