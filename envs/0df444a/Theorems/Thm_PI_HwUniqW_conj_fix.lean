-- Prove2me | Theorems.Thm_PI_HwUniqW_conj_fix
-- name    : PI.HwUniqW.conj_fix
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:29:29.517602+00:00
-- url     : https://prove2.me/theorems/ef938e43-c234-451f-8496-feb6df239507
-- title:
--   Hw Uniq W: conj fix
-- statement:
--   The Hw Uniq W construction uses the conj fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L90-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightUniqueness/FrameInvMulVecNegativeVector.lean#L90-L100

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}

theorem PI.HwUniqW.conj_fix {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) : FixEW k r (g⁻¹ * x * g) := by sorry
