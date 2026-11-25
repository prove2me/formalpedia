-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_dkl
-- name    : PositivityTheory.Rg.Sw.WR.Ib.ibp_dkl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:05:27.288073+00:00
-- url     : https://prove2.me/theorems/2ccfe059-e5f3-563b-8680-d8fbcb8d0514
-- title:
--   Ib: ibp dkl
-- statement:
--   The Ib construction uses the ibp dkl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L154-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L154-L177

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

theorem PositivityTheory.Rg.Sw.WR.Ib.ibp_dkl {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (k l : Fin n)
    (h1 : Integrable (Dkl k l g)) (h2 : Integrable (Dkl l k g)) (t : ℝ) (β : E n) :
    ∫ y, Dkl k l g y * chr t β y = -((-(Complex.I * t)) * herm β k l) * ∫ y, g y * chr t β y := by sorry
