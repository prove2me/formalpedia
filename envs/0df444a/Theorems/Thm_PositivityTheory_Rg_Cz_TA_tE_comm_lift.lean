-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TA_tE_comm_lift
-- name    : PositivityTheory.Rg.Cz.TA.tE_comm_lift
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:43.477352+00:00
-- url     : https://prove2.me/theorems/407ebb68-659c-46cc-b3f1-956799a88c63
-- title:
--   TA: t E comm lift
-- statement:
--   The TA construction uses the t E comm lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean#L68-L78

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P]

theorem PositivityTheory.Rg.Cz.TA.tE_comm_lift (S : Finset P) (F : Fin n → Fin n → Module.End ℂ M) (B : Module.End ℂ M)
    (h : ∀ c d, Commute (F c d) B) (a b : Fin n) :
    Commute (tE S F a b : Module.End ℂ (TV n M P)) (lift B) := by sorry
