-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_lift_comm_mAt
-- name    : PositivityTheory.Rg.Cz.TGK.lift_comm_mAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:46.453735+00:00
-- url     : https://prove2.me/theorems/c5299e23-59f9-5c36-a937-304f1b929aec
-- title:
--   TGK: lift comm m At
-- statement:
--   The TGK construction uses the lift comm m At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L35-L38

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem PositivityTheory.Rg.Cz.TGK.lift_comm_mAt (B : Module.End ℂ M) (p : P) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute (lift B) (mAt p A : Module.End ℂ (TV n M P)) := by sorry
