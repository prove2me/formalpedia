-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_lf_re_im
-- name    : PositivityTheory.Rg.Sw.WR.Ib.lf_re_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:50:35.752867+00:00
-- url     : https://prove2.me/theorems/b0b96e96-685b-4b93-80e2-aca1bee2f428
-- title:
--   Ib: lf re im
-- statement:
--   The Ib construction uses the lf re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/IntegrableOfBound.lean#L56-L66

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

theorem PositivityTheory.Rg.Sw.WR.Ib.lf_re_im (t : ℝ) (β : E n) (w : Fin n → Fin n → ℂ) :
    lf t β (fun a b => (w a b).re) + Complex.I * lf t β (fun a b => (w a b).im) =
      -(Complex.I * t * ∑ a, ∑ b, (β a b : ℂ) * w a b) := by sorry
