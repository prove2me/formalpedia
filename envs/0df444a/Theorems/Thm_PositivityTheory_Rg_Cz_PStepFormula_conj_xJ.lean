-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_conj_xJ
-- name    : PositivityTheory.Rg.Cz.PStepFormula.conj_xJ
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:21.89928+00:00
-- url     : https://prove2.me/theorems/6d688684-5aed-4773-92e6-a2b4026b5eb9
-- title:
--   PStep Formula: conj x J
-- statement:
--   The PStep Formula construction uses the conj x J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L194-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L194-L203

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

theorem PositivityTheory.Rg.Cz.PStepFormula.conj_xJ {N : ℕ} (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E)
    (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    (pm σ * xJ E k * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) =
      Om E (σ k) + ∑ i ∈ Finset.univ.filter (· < k), pm (Equiv.swap (σ i) (σ k)) := by sorry
