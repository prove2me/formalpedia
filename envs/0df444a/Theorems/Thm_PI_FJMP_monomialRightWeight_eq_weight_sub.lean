-- Prove2me | Theorems.Thm_PI_FJMP_monomialRightWeight_eq_weight_sub
-- name    : PI.FJMP.monomialRightWeight_eq_weight_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:02.951674+00:00
-- url     : https://prove2.me/theorems/dd03f25b-3626-4ffd-8a8c-a6b145f71f98
-- title:
--   FJMP: monomial Right Weight eq weight sub
-- statement:
--   The FJMP construction uses the monomial Right Weight eq weight sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L259-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L259-L280

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

theorem PI.FJMP.monomialRightWeight_eq_weight_sub (hW : FormWt2) {p q r s : ℕ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct2 p q r s) μ') (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (c : Ix r s) :
    ((wt2 e c : ℤ) : ℚ) = nu2 p q r s μ' c := by sorry
