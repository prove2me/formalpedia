-- Prove2me | Theorems.Thm_PI_IsoFunVW_prod_sum_cc
-- name    : PI.IsoFunVW.prod_sum_cc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:52.817798+00:00
-- url     : https://prove2.me/theorems/4fddf351-0c84-4406-9467-d44b4bef80e7
-- title:
--   Iso Fun VW: prod sum cc
-- statement:
--   The Iso Fun VW construction uses the prod sum cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L66-L71

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

theorem PI.IsoFunVW.prod_sum_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {R : Type} [CommRing R] (N : ℕ)
    (nu : Lt → YoungDiagram)
    (F : ∀ (z : Lt) (c : Fin ((nu z).rowLen 0)), (Fin ((nu z).colLen c) ↪o Fin N) → R) :
    ∏ z, ∏ c, ∑ Jc, F z c Jc = ∑ J : ColChoice N nu, ∏ z, ∏ c, F z c (J z c) := by sorry
