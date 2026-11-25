-- Prove2me | Theorems.Thm_PI_FJMP_gR_pos_lemma
-- name    : PI.FJMP.gR_pos_lemma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:19.397071+00:00
-- url     : https://prove2.me/theorems/47549d7e-c11b-4fe3-8edd-bb60be1374ed
-- title:
--   FJMP: g R pos lemma
-- statement:
--   The FJMP construction uses the g R pos lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L100-L117

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

theorem PI.FJMP.gR_pos_lemma (u v : κ → σ) (pos : κ → Bool) (hu : Function.Injective u) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = true → NoVar P (u c))
    (c0 : κ) (hc0 : pos c0 = true) : pderiv (v c0) P = 0 := by sorry
