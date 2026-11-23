-- Prove2me | Theorems.Thm_PI_TOW_combo_smul
-- name    : PI.TOW.combo_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:14.283659+00:00
-- url     : https://prove2.me/theorems/e3ea0dd9-85ab-4143-94ab-ef9c7a9923df
-- title:
--   TOW: combo smul
-- statement:
--   The TOW construction uses the combo smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L118-L123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO
variable {K : Type} [CommRing K] {n' k : ℕ}

theorem PI.TOW.combo_smul (a : K) (f : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (a • f) G = a • combo f G := by sorry
