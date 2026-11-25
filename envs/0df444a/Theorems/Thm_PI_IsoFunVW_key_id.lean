-- Prove2me | Theorems.Thm_PI_IsoFunVW_key_id
-- name    : PI.IsoFunVW.key_id
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:01.09808+00:00
-- url     : https://prove2.me/theorems/97bdab58-6853-4a62-986b-6342abd1b01d
-- title:
--   Iso Fun VW: key id
-- statement:
--   The Iso Fun VW construction uses the key id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L73-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L73-L108

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

theorem PI.IsoFunVW.key_id {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) (I : ColChoice N' nu) :
    ∑ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) = minY N' nu I (yfr tp s x) := by sorry
