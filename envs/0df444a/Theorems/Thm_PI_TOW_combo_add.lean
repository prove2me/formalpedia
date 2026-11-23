-- Prove2me | Theorems.Thm_PI_TOW_combo_add
-- name    : PI.TOW.combo_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:20.777817+00:00
-- url     : https://prove2.me/theorems/ffec46ce-55a0-4bdb-869e-3ad4cd5ebcad
-- title:
--   TOW: combo add
-- statement:
--   The TOW construction uses the combo add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L113-L116

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

theorem PI.TOW.combo_add (f₁ f₂ : List (Fin n' × (Fin k × Fin k)) →₀ K) (G : MvPolynomial (Fin n' × Fin k) K) :
    combo (f₁ + f₂) G = combo f₁ G + combo f₂ G := by sorry
