-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_trace_im_zero
-- name    : PositivityTheory.Rg.Sw.WR.G.GM.trace_im_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:04:13.112163+00:00
-- url     : https://prove2.me/theorems/f636007c-623b-5860-8569-f3ffd621dc75
-- title:
--   GM: trace im zero
-- statement:
--   The GM construction uses the trace im zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/GaussM.lean#L28-L34

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM

theorem PositivityTheory.Rg.Sw.WR.G.GM.trace_im_zero {b Q : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (hQ : Q.IsHermitian) :
    (b * Q).trace.im = 0 := by sorry
