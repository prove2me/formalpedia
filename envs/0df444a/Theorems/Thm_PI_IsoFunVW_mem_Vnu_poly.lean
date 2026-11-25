-- Prove2me | Theorems.Thm_PI_IsoFunVW_mem_Vnu_poly
-- name    : PI.IsoFunVW.mem_Vnu_poly
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:02:13.749141+00:00
-- url     : https://prove2.me/theorems/626b7bdd-8688-5bc4-bdf1-7f59a97e7cfd
-- title:
--   Iso Fun VW: mem Vnu poly
-- statement:
--   The Iso Fun VW construction uses the mem Vnu poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L125-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryFunctionSpace/InstFintypeOE.lean#L125-L152

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

theorem PI.IsoFunVW.mem_Vnu_poly {Lt σ : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (y : Lt → Fin N → ℕ → MvPolynomial σ ℂ) :
    (fun I => L (minY N nu I y)) ∈ Vnu N nu := by sorry
