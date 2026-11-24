-- Prove2me | Theorems.Thm_PI_FJMS_pure_of
-- name    : PI.FJMS.pure_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:20.523906+00:00
-- url     : https://prove2.me/theorems/8c7e8df7-d226-4078-9d58-3d134ee30b20
-- title:
--   FJMS: pure of
-- statement:
--   The FJMS construction uses the pure of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PosIffLtNP.lean#L134-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP
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
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}

theorem PI.FJMS.pure_of (hM : MinHyp p q r s μ μ' P) {e : Ln p q r s →₀ ℕ} (he : e ∈ P.support) {l : Ln p q r s}
    (hl : e l ≠ 0) : nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
      (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2) := by sorry
