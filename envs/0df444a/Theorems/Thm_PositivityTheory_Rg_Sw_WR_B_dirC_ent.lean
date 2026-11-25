-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_ent
-- name    : PositivityTheory.Rg.Sw.WR.B.dirC_ent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:00:22.761241+00:00
-- url     : https://prove2.me/theorems/ae61c7a2-9930-497c-8963-ac5526d4cd12
-- title:
--   B: dir C ent
-- statement:
--   The B construction uses the dir C ent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L191-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MollifiedIntegrability/ClsBound.lean#L191-L200

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

theorem PositivityTheory.Rg.Sw.WR.B.dirC_ent {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (k l : Fin n) (e : Bool × Fin n × Fin n) :
    dirC (ent s e) (vkl k l) y = MvPolynomial.eval (fun e => ent s e y) (dEnt s k l e) := by sorry
