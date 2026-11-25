-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_WbDefC_jpq_mulVec_of_inr
-- name    : PI.UnitaryGroupMassFormula.CntFormula.WbDefC.jpq_mulVec_of_inr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:31:53.709936+00:00
-- url     : https://prove2.me/theorems/e41e9c05-745f-4f57-8514-ff488dab5cc4
-- title:
--   Wb Def C: jpq mul Vec of inr
-- statement:
--   The Wb Def C construction uses the jpq mul Vec of inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_MiscLemmasI_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_CTEqConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.WbDefC

theorem PI.UnitaryGroupMassFormula.CntFormula.WbDefC.jpq_mulVec_of_inr {p q : ℕ} (w : Fin p ⊕ Fin q → ℂ) (hw : ∀ j, w (Sum.inr j) = 0) :
    Formalism.UG.Jpq p q *ᵥ w = w := by sorry
