-- Prove2me | Theorems.Thm_PI_FHS_mixed2
-- name    : PI.FHS.mixed2
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:36.342073+00:00
-- url     : https://prove2.me/theorems/7bf84a22-41c6-4b5d-9ab4-44acb5cd506e
-- title:
--   FHS: mixed2
-- statement:
--   The FHS construction uses the mixed2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L116-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L116-L126

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

theorem PI.FHS.mixed2 {Z : Mat r s} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by sorry
