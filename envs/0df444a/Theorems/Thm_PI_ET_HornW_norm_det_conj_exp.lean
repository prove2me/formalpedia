-- Prove2me | Theorems.Thm_PI_ET_HornW_norm_det_conj_exp
-- name    : PI.ET.HornW.norm_det_conj_exp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:45.945887+00:00
-- url     : https://prove2.me/theorems/e1d036c4-bdff-4113-bfc7-76cbd92cbe94
-- title:
--   Horn W: norm det conj exp
-- statement:
--   The Horn W construction uses the norm det conj exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L66-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}

theorem PI.ET.HornW.norm_det_conj_exp {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℝ) :
    ‖(W * diagonal (fun i => (Real.exp (d i) : ℂ)) * Wᴴ).det‖ = Real.exp (∑ i, d i) := by sorry
