-- Prove2me | Theorems.Thm_PI_ET_HornW_conj_herm
-- name    : PI.ET.HornW.conj_herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:07.099066+00:00
-- url     : https://prove2.me/theorems/9abd331c-48af-4f30-8270-2c5ee704802e
-- title:
--   Horn W: conj herm
-- statement:
--   The Horn W construction uses the conj herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/NormDetConjExp.lean#L32-L38

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

theorem PI.ET.HornW.conj_herm (W : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → ℝ) :
    (W * diagonal (fun i => (r i : ℂ)) * Wᴴ)ᴴ = W * diagonal (fun i => (r i : ℂ)) * Wᴴ := by sorry
