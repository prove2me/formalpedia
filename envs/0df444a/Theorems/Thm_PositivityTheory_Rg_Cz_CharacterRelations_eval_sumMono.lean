-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_CharacterRelations_eval_sumMono
-- name    : PositivityTheory.Rg.Cz.CharacterRelations.eval_sumMono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:15.027805+00:00
-- url     : https://prove2.me/theorems/e69a22e5-fa11-4b35-ad9e-6d426cde113f
-- title:
--   Character Relations: eval sum Mono
-- statement:
--   The Character Relations construction uses the eval sum Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepChar.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepChar.lean#L23-L26

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

theorem PositivityTheory.Rg.Cz.CharacterRelations.eval_sumMono (d : ℕ → A) (N : ℕ) (u : ℂ) :
    (∑ i ∈ Finset.range N, monomial i (d i)).eval (algebraMap ℂ A u) = ∑ i ∈ Finset.range N, u ^ i • d i := by sorry
