-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_eval_mul_nc
-- name    : PositivityTheory.Rg.Cz.CharacterRelations.eval_mul_nc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:48:21.887307+00:00
-- url     : https://prove2.me/theorems/ddcc2a22-a126-4804-9138-58a4a06f115e
-- title:
--   Character Relations: eval mul nc
-- statement:
--   The Character Relations construction uses the eval mul nc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepChar.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepChar.lean#L19-L21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.CharacterRelations
variable {A : Type*} [Ring A] [Algebra ℂ A]
set_option linter.unusedSectionVars false

theorem PositivityTheory.Rg.Cz.CharacterRelations.eval_mul_nc (p q : A[X]) (x : A) (h : ∀ k, Commute (q.coeff k) x) :
    (p * q).eval x = p.eval x * q.eval x := by sorry
