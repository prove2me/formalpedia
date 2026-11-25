-- Prove2me | Theorems.Thm_PI_ET_HornW_conj_mul_conj
-- name    : PI.ET.HornW.conj_mul_conj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:52.504994+00:00
-- url     : https://prove2.me/theorems/36b78561-5448-42e8-9b62-bb0faacbd24c
-- title:
--   Horn W: conj mul conj
-- statement:
--   The Horn W construction uses the conj mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L24-L30

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

theorem PI.ET.HornW.conj_mul_conj {W : Matrix (Fin n) (Fin n) ℂ} (hW : W ∈ unitaryGroup (Fin n) ℂ)
    (d e : Fin n → ℂ) :
    (W * diagonal d * Wᴴ) * (W * diagonal e * Wᴴ) = W * diagonal (fun i => d i * e i) * Wᴴ := by sorry
