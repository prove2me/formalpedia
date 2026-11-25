-- Prove2me | Theorems.Thm_PI_FHS_omAct_adj
-- name    : PI.FHS.omAct_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:04.508908+00:00
-- url     : https://prove2.me/theorems/e7ff95f3-a33f-4ce5-abf0-0836375bac21
-- title:
--   FHS: om Act adj
-- statement:
--   The FHS construction uses the om Act adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L74-L87

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

theorem PI.FHS.omAct_adj (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (hM : Mixed M) (P Q : Pol p q r s) :
    fockInner (omAct p q r s M P) Q = - fockInner P (omAct p q r s Mᴴ Q) := by sorry
