-- Prove2me | Theorems.Thm_PI_IsoFunVW_linW_apply
-- name    : PI.IsoFunVW.linW_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:27.0168+00:00
-- url     : https://prove2.me/theorems/0526e709-9723-4725-8c11-13da60a7b280
-- title:
--   Iso Fun VW: lin W apply
-- statement:
--   The Iso Fun VW construction uses the lin W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L44-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV

theorem PI.IsoFunVW.linW_apply {σ : Type} (w : (σ →₀ ℕ) → ℂ) (P : MvPolynomial σ ℂ) :
    linW w P = ∑ α ∈ P.support, coeff α P * w α := by sorry
