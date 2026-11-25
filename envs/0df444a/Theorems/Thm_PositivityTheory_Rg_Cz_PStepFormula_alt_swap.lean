-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_alt_swap
-- name    : PositivityTheory.Rg.Cz.PStepFormula.alt_swap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:48:01.203077+00:00
-- url     : https://prove2.me/theorems/ac487b77-4ba2-5e81-aec3-95f37338c9e9
-- title:
--   PStep Formula: alt swap
-- statement:
--   The PStep Formula construction uses the alt swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PStepFormulaA.lean#L88-L96

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

theorem PositivityTheory.Rg.Cz.PStepFormula.alt_swap {X : Type} [AddCommGroup X] [Module ℂ X] (g : TV n X (Fin n)) (J : Fin n → Fin n) (a b : Fin n)
    (h : a ≠ b) : alt Finset.univ g (J ∘ Equiv.swap a b) = -alt Finset.univ g J := by sorry
