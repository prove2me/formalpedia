-- Prove2me | Theorems.Thm_PI_FJMP_monomialLeftWeight_eq_weight_sub
-- name    : PI.FJMP.monomialLeftWeight_eq_weight_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:37.04817+00:00
-- url     : https://prove2.me/theorems/72e62b78-6e36-4d7c-bec8-5aa8d9baef87
-- title:
--   FJMP: monomial Left Weight eq weight sub
-- statement:
--   The FJMP construction uses the monomial Left Weight eq weight sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L236-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L236-L257

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

theorem PI.FJMP.monomialLeftWeight_eq_weight_sub (hW : FormWt1) {p q r s : ℕ} {μ : Ix p q → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (a : Ix p q) :
    ((wt1 e a : ℤ) : ℚ) = nu1 p q r s μ a := by sorry
