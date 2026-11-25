-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_sum_lt_cast
-- name    : PositivityTheory.Rg.Cz.PStepFormula.sum_lt_cast
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:54.512846+00:00
-- url     : https://prove2.me/theorems/47aac605-aca6-4df1-bb52-f47ed85ec753
-- title:
--   PStep Formula: sum lt cast
-- statement:
--   The PStep Formula construction uses the sum lt cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L162-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L162-L175

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

theorem PositivityTheory.Rg.Cz.PStepFormula.sum_lt_cast {X : Type} [AddCommMonoid X] (k : Fin (1 + n)) (hk : (k : ℕ) ≤ n) (f : Fin (1 + n) → X) :
    ∑ i ∈ Finset.univ.filter (· < k), f i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f ⟨i, by omega⟩ := by sorry
