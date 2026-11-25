-- Prove2me | Theorems.Thm_PI_FJMP_seg_neg_gen
-- name    : PI.FJMP.seg_neg_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:45.740267+00:00
-- url     : https://prove2.me/theorems/43aae5d3-39f3-4883-a94e-d4ba71696e39
-- title:
--   FJMP: seg neg gen
-- statement:
--   The FJMP construction uses the seg neg gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L153-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L153-L181

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
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
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
variable {κ : Type*} [Fintype κ]

theorem PI.FJMP.seg_neg_gen (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwU : ∀ e ∈ P.support, (sw e u pos : ℚ) = nuU)
    (hpV : ∀ e ∈ P.support, ∀ c, e (v c) ≠ 0 → nuV ≠ 0 ∧ (pos c = true ↔ 0 < nuV)) (hU : nuU < 0) :
    nuV < 0 := by sorry
