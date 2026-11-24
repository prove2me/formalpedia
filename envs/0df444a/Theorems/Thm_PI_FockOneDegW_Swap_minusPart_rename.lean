-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_minusPart_rename
-- name    : PI.FockOneDegW.Swap.minusPart_rename
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:47.860029+00:00
-- url     : https://prove2.me/theorems/7ea6d7d5-2f76-4ffe-b01b-0f2515b9cf2c
-- title:
--   Swap: minus Part rename
-- statement:
--   The Swap construction uses the minus Part rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L78-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L78-L92

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {σ τ : Type*} (f : σ ≃ τ)

theorem PI.FockOneDegW.Swap.minusPart_rename (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (hAB : ∀ Q, B (rename f Q) = rename f (A Q))
    (P : MvPolynomial σ ℂ) : rename f (minusPart A P) = minusPart B (rename f P) := by sorry
