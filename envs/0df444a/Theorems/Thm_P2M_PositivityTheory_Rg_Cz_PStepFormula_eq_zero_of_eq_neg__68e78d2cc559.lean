-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559
-- name    : P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:58.026316+00:00
-- url     : https://prove2.me/theorems/21c8705c-7496-452b-8e8d-92125cdac55b
-- title:
--   P2 M Positivity Theory Rg Cz PStep Formula eq zero of eq neg  68e78d2cc559: P2 M Positivity Theory Rg Cz PStep Formula eq zero of eq neg  68e78d2cc559
-- statement:
--   The P2 M Positivity Theory Rg Cz PStep Formula eq zero of eq neg  68e78d2cc559 construction uses the P2 M Positivity Theory Rg Cz PStep Formula eq zero of eq neg  68e78d2cc559 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L81-L86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
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
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559 {X : Type} [AddCommGroup X] [Module ℂ X] {x : X} (h : x = -x) : x = 0 := by sorry

alias «PositivityTheory».«Rg».«Cz».«PStepFormula».«eq_zero_of_eq_neg'» := P2M_PositivityTheory_Rg_Cz_PStepFormula_eq_zero_of_eq_neg__68e78d2cc559
