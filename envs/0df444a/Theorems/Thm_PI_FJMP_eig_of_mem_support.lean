-- Prove2me | Theorems.Thm_PI_FJMP_eig_of_mem_support
-- name    : PI.FJMP.eig_of_mem_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:48.990193+00:00
-- url     : https://prove2.me/theorems/29247682-fc47-46a5-8281-7a41963cff63
-- title:
--   FJMP: eig of mem support
-- statement:
--   The FJMP construction uses the eig of mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L32-L38

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

theorem PI.FJMP.eig_of_mem_support (T : Module.End ℂ (MvPolynomial σ ℂ)) (w : (σ →₀ ℕ) → ℂ)
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (c : ℂ) (hP : T P = c • P)
    (e : σ →₀ ℕ) (he : e ∈ P.support) : w e = c := by sorry
