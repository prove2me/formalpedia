-- Prove2me | Theorems.Thm_PI_FJMP_coeff_diag
-- name    : PI.FJMP.coeff_diag
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:03.074124+00:00
-- url     : https://prove2.me/theorems/6528df6e-8003-4662-bcb9-7435c8eccb9f
-- title:
--   FJMP: coeff diag
-- statement:
--   The FJMP construction uses the coeff diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L15-L30

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

theorem PI.FJMP.coeff_diag (T : Module.End ℂ (MvPolynomial σ ℂ)) (w : (σ →₀ ℕ) → ℂ)
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (e : σ →₀ ℕ) :
    coeff e (T P) = w e * coeff e P := by sorry
