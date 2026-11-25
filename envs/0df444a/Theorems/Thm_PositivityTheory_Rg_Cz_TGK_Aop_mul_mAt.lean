-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_Aop_mul_mAt
-- name    : PositivityTheory.Rg.Cz.TGK.Aop_mul_mAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:58:21.47523+00:00
-- url     : https://prove2.me/theorems/243b27b4-f55a-53e6-b1b2-201691bd9ede
-- title:
--   TGK: Aop mul m At
-- statement:
--   The TGK construction uses the Aop mul m At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L106-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L106-L138

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

theorem PositivityTheory.Rg.Cz.TGK.Aop_mul_mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop K * mAt p A : Module.End ℂ (TV n M P)) = Aop (Function.update K p (K p * A)) := by sorry
