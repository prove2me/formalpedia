-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TF_rc_comm
-- name    : PositivityTheory.Rg.Cz.TF.rc_comm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:39.727041+00:00
-- url     : https://prove2.me/theorems/51e5cc3c-9108-4c07-8077-d8fda81aba4f
-- title:
--   TF: rc comm
-- statement:
--   The TF construction uses the rc comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean#L17-L22

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
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
open PositivityTheory.Rg.Cz.TF

theorem PositivityTheory.Rg.Cz.TF.rc_comm {W : Type*} [AddCommGroup W] [Module ℂ W] (A B : Module.End ℂ W) (h : Commute A B) :
    Commute (rc A) (rc B) := by sorry
