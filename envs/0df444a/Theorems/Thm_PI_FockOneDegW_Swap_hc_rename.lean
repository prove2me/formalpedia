-- Prove2me | Theorems.Thm_PI_FockOneDegW_Swap_hc_rename
-- name    : PI.FockOneDegW.Swap.hc_rename
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:35.714273+00:00
-- url     : https://prove2.me/theorems/539008fc-1be6-4d9f-853d-f62f456c05ca
-- title:
--   Swap: hc rename
-- statement:
--   The Swap construction uses the hc rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L64-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/KroneckerOneRightSwap.lean#L64-L76

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW PI.FockOneDegW.Swap
open PI.FockOneDegW PI.FockOneDegW.Diag
variable {σ τ : Type*} (f : σ ≃ τ)

theorem PI.FockOneDegW.Swap.hc_rename (φ : MvPolynomial σ ℂ) (k : ℕ) :
    homogeneousComponent k (rename f φ) = rename f (homogeneousComponent k φ) := by sorry
