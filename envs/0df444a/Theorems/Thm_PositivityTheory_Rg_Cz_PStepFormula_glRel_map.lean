-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_glRel_map
-- name    : PositivityTheory.Rg.Cz.PStepFormula.glRel_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:27.809535+00:00
-- url     : https://prove2.me/theorems/64c688bc-1cc9-4b05-a4d9-de1926c2d7d6
-- title:
--   PStep Formula: gl Rel map
-- statement:
--   The PStep Formula construction uses the gl Rel map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L16-L20

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

theorem PositivityTheory.Rg.Cz.PStepFormula.glRel_map {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (fun a b => f (E a b)) := by sorry
