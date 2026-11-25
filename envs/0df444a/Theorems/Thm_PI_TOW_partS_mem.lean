-- Prove2me | Theorems.Thm_PI_TOW_partS_mem
-- name    : PI.TOW.partS_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:11.360166+00:00
-- url     : https://prove2.me/theorems/781ba93d-463d-4f92-bab2-a029436512c5
-- title:
--   TOW: part S mem
-- statement:
--   The TOW construction uses the part S mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FilterConcatWLength.lean#L35-L45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
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

theorem PI.TOW.partS_mem {K : Type} [CommRing K] {n' m : ℕ} {d : Fin n' → ℕ} (μ : Fin n' × Fin (m + 1) →₀ ℕ)
    (hμ : μ ∈ {μ : Fin n' × Fin (m + 1) →₀ ℕ | ∀ i, multideg μ i = d i}) (t : Fin n') :
    monomial (partS μ t) (1 : K) ∈ Hd K (m + 1) (d t) := by sorry
