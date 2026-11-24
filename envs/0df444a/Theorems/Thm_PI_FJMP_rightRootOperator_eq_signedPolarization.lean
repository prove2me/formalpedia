-- Prove2me | Theorems.Thm_PI_FJMP_rightRootOperator_eq_signedPolarization
-- name    : PI.FJMP.rightRootOperator_eq_signedPolarization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:15.420867+00:00
-- url     : https://prove2.me/theorems/2081eee0-2b97-41f1-b554-845684a664a1
-- title:
--   FJMP: right Root Operator eq signed Polarization
-- statement:
--   The FJMP construction uses the right Root Operator eq signed Polarization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L376-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/MemLeftHighestWeightOfIsMinimalJointVector.lean#L376-L392

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

theorem PI.FJMP.rightRootOperator_eq_signedPolarization {p q r s : ℕ} (c d : Ix r s) (hcd : c ≠ d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) (P : Pol p q r s) :
    rai2 (p := p) (q := q) c d P = gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) P := by sorry
