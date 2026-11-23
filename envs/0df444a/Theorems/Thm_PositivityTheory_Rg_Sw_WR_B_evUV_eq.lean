-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_evUV_eq
-- name    : PositivityTheory.Rg.Sw.WR.B.evUV_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:05.365872+00:00
-- url     : https://prove2.me/theorems/078c0f52-846e-4380-a281-ccc262a9c2af
-- title:
--   B: ev UV eq
-- statement:
--   The B construction uses the ev UV eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L177-L178

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.WR.B.evUV_eq (s : ℂ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (y : E n) :
    evUV s R y = MvPolynomial.eval (fun e => ent s e y) R := by sorry
