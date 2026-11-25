-- Prove2me | Theorems.Thm_PI_FJMP_gR_neg_lemma
-- name    : PI.FJMP.gR_neg_lemma
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:13.844059+00:00
-- url     : https://prove2.me/theorems/6658a501-b7d4-5462-8d45-bdcc6816188b
-- title:
--   FJMP: g R neg lemma
-- statement:
--   The FJMP construction uses the g R neg lemma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L119-L124

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

theorem PI.FJMP.gR_neg_lemma (u v : κ → σ) (pos : κ → Bool) (hv : Function.Injective v) (huv : ∀ c c', u c ≠ v c')
    (P : MvPolynomial σ ℂ) (hR : gR u v pos P = 0) (hno : ∀ c, pos c = false → NoVar P (v c))
    (c0 : κ) (hc0 : pos c0 = false) : pderiv (u c0) P = 0 := by sorry
