-- Prove2me | Theorems.Thm_PI_IsoFunVW_applyAt0_eq
-- name    : PI.IsoFunVW.applyAt0_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:52.376838+00:00
-- url     : https://prove2.me/theorems/11fa218d-29cf-5a68-8cb5-74e88d607b89
-- title:
--   Iso Fun VW: apply At0 eq
-- statement:
--   The Iso Fun VW construction uses the apply At0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L50-L54

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

theorem PI.IsoFunVW.applyAt0_eq {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ)
    (Θ : VC T N N' → ℂ) : applyAt0 P Θ = linW (wTh Θ) P := by sorry
