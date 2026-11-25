-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_one
-- name    : PositivityTheory.Rg.Cz.PStepFormula.one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:47.383822+00:00
-- url     : https://prove2.me/theorems/1e91622d-e444-492f-9139-f9f8a720a7c5
-- title:
--   PStep Formula: one
-- statement:
--   The PStep Formula construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormula.lean#L13-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormula.lean#L13-L96

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormula
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

theorem PositivityTheory.Rg.Cz.PStepFormula.one (hT : TensorGl) (hJ : JMComm) (hQ : PiQdet) (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : GlRel E) (u : ℂ) :
    (PiJ 1 E u * qdet (tE (Finset.univ : Finset (Fin 1)) E) u : Module.End ℂ (TV n M (Fin 1))) =
      lift (qdet E u) * PiJ 1 E (u + 1) := by sorry
