-- Prove2me | Theorems.Thm_PI_FHS_fockAct1_eq
-- name    : PI.FHS.fockAct1_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:49.365366+00:00
-- url     : https://prove2.me/theorems/88a53fb4-ab1c-4fd8-bf3d-fc54a13acbed
-- title:
--   FHS: fock Act1 eq
-- statement:
--   The FHS construction uses the fock Act1 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L96-L98

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

theorem PI.FHS.fockAct1_eq (Z : Mat p q) :
    fockAct1 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by sorry
