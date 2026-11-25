-- Prove2me | Theorems.Thm_PI_FockOneDegW_HwC_exists_wtvec
-- name    : PI.FockOneDegW.HwC.exists_wtvec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:17.022002+00:00
-- url     : https://prove2.me/theorems/265a3075-f7fb-4ad4-8a91-915da5b7d4eb
-- title:
--   Hw C: exists wtvec
-- statement:
--   The Hw C construction uses the exists wtvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/HighestWeightExists.lean#L11-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockDegreeOne/HighestWeightExists.lean#L11-L68

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_HighestWeightExists
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
open PI PI.FockOneDegW PI.FockOneDegW.HwC
open Classical

theorem PI.FockOneDegW.HwC.exists_wtvec {p q r s : ℕ} (U : Submodule ℂ (Pol p q r s))
    (hU : ∀ c : Ix p q, ∀ u ∈ U, fockAct1 p q r s (Eab c c) u ∈ U) :
    ∀ (n : ℕ) (u : Pol p q r s), u ∈ U → u ≠ 0 → (u.support.image wtv).card ≤ n →
      ∃ (ν : Ix p q → ℚ) (v : Pol p q r s), v ∈ U ∧ v ≠ 0 ∧ IsWt ν v ∧ v.support ⊆ u.support := by sorry
