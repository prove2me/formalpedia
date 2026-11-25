-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_ibp_dir
-- name    : PositivityTheory.Rg.Sw.WR.Ib.ibp_dir
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:50.316264+00:00
-- url     : https://prove2.me/theorems/10b6bbc3-b992-4799-9705-bf024ab36334
-- title:
--   Ib: ibp dir
-- statement:
--   The Ib construction uses the ibp dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L133-L152

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

theorem PositivityTheory.Rg.Sw.WR.Ib.ibp_dir {g : E n → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgi : Integrable g) (w : E n)
    (hgw : Integrable fun y => fderiv ℝ g y w) (t : ℝ) (β : E n) :
    ∫ y, fderiv ℝ g y w * chr t β y = -(lf t β w) * ∫ y, g y * chr t β y := by sorry
