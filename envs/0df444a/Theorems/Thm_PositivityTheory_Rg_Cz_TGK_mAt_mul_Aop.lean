-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_TGK_mAt_mul_Aop
-- name    : PositivityTheory.Rg.Cz.TGK.mAt_mul_Aop
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:08.742896+00:00
-- url     : https://prove2.me/theorems/7771a295-2cfa-521d-aaf7-c1193b1bb3cc
-- title:
--   TGK: m At mul Aop
-- statement:
--   The TGK construction uses the m At mul Aop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean#L87-L104

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

theorem PositivityTheory.Rg.Cz.TGK.mAt_mul_Aop (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (mAt p A * Aop K : Module.End ℂ (TV n M P)) = Aop (Function.update K p (A * K p)) := by sorry
