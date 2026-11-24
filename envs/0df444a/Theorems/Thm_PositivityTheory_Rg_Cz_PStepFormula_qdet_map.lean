-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_qdet_map
-- name    : PositivityTheory.Rg.Cz.PStepFormula.qdet_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:24.553734+00:00
-- url     : https://prove2.me/theorems/e0fb7a60-a350-4475-a2b2-a8d83eff3fe3
-- title:
--   PStep Formula: qdet map
-- statement:
--   The PStep Formula construction uses the qdet map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L11-L14

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

theorem PositivityTheory.Rg.Cz.PStepFormula.qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : f (qdet E u) = qdet (fun a b => f (E a b)) u := by sorry
