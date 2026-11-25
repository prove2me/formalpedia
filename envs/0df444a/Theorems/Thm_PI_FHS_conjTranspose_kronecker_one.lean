-- Prove2me | Theorems.Thm_PI_FHS_conjTranspose_kronecker_one
-- name    : PI.FHS.conjTranspose_kronecker_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:06.233692+00:00
-- url     : https://prove2.me/theorems/450ddfc8-4e5e-4ecd-a678-443674293653
-- title:
--   FHS: conj Transpose kronecker one
-- statement:
--   The FHS construction uses the conj Transpose kronecker one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L128-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L128-L135

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

theorem PI.FHS.conjTranspose_kronecker_one (Z : Mat p q) :
    (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s))ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) Zᴴ (1 : Mat r s) := by sorry
