-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_WbDefC_sigNeg_card_le
-- name    : PI.UnitaryGroupMassFormula.CntFormula.WbDefC.sigNeg_card_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:31:27.565818+00:00
-- url     : https://prove2.me/theorems/837ca4a3-6cb5-57eb-9939-739b700af317
-- title:
--   Wb Def C: sig Neg card le
-- statement:
--   The Wb Def C construction uses the sig Neg card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L25-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/CTEqConjTranspose.lean#L25-L79

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

theorem PI.UnitaryGroupMassFormula.CntFormula.WbDefC.sigNeg_card_le {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    (J : Matrix n n ℂ) (p q : ℕ) (hJ : Formalism.UG.HasSignature J p q) (u : ι → n → ℂ)
    (hu : LinearIndependent ℂ u)
    (hneg : ∀ d : ι → ℂ, (star (∑ a, d a • u a) ⬝ᵥ (J *ᵥ ∑ a, d a • u a)).re ≤ 0) :
    Fintype.card ι ≤ q := by sorry
