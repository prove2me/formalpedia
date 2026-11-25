-- Prove2me | Theorems.Thm_PI_FJMP_seg_pos_gen
-- name    : PI.FJMP.seg_pos_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:37.730317+00:00
-- url     : https://prove2.me/theorems/1e794ef2-8293-42d7-b525-0c53a8f287f6
-- title:
--   FJMP: seg pos gen
-- statement:
--   The FJMP construction uses the seg pos gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L126-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L126-L151

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

theorem PI.FJMP.seg_pos_gen (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hP : P ≠ 0) (nuU nuV : ℚ)
    (hwV : ∀ e ∈ P.support, (sw e v pos : ℚ) = nuV)
    (hpU : ∀ e ∈ P.support, ∀ c, e (u c) ≠ 0 → nuU ≠ 0 ∧ (pos c = true ↔ 0 < nuU)) (hV : 0 < nuV) :
    0 < nuU := by sorry
