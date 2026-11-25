-- Prove2me | Theorems.Thm_PI_MSC_card_fiber
-- name    : PI.MSC.card_fiber
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:52.456312+00:00
-- url     : https://prove2.me/theorems/af65ae70-f33a-4976-8f16-30738d396469
-- title:
--   MSC: card fiber
-- statement:
--   The MSC construction uses the card fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L38-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean#L38-L53

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.MSC

theorem PI.MSC.card_fiber {γ : Type*} [Fintype γ] (h : γ → ℕ) {v : ℕ} (hv : 0 < v) :
    (Finset.univ.filter fun x => h x = v).card + (Finset.univ.filter fun x => v < h x).card =
      (Finset.univ.filter fun x => v - 1 < h x).card := by sorry
