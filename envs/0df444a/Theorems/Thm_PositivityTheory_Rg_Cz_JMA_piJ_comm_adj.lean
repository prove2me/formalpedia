-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_JMA_piJ_comm_adj
-- name    : PositivityTheory.Rg.Cz.JMA.piJ_comm_adj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:44.946264+00:00
-- url     : https://prove2.me/theorems/d56bb84d-7a68-4bef-be01-468f91159d46
-- title:
--   JMA: pi J comm adj
-- statement:
--   The JMA construction uses the pi J comm adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L168-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PJmComm.lean#L168-L182

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem PositivityTheory.Rg.Cz.JMA.piJ_comm_adj (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (u : ℂ)
    (i : Fin m) : Commute (PiJ (m + 1) E u) (pm (Equiv.swap i.castSucc i.succ)) := by sorry
