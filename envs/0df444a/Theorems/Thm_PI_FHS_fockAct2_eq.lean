-- Prove2me | Theorems.Thm_PI_FHS_fockAct2_eq
-- name    : PI.FHS.fockAct2_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:56.303775+00:00
-- url     : https://prove2.me/theorems/73316868-b41c-48e3-956c-69a429c0389b
-- title:
--   FHS: fock Act2 eq
-- statement:
--   The FHS construction uses the fock Act2 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L100-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L100-L102

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {p q r s : ℕ}

theorem PI.FHS.fockAct2_eq (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by sorry
