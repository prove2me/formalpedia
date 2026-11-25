-- Prove2me | Theorems.Thm_PI_FHS_mixed1
-- name    : PI.FHS.mixed1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:44.09632+00:00
-- url     : https://prove2.me/theorems/79a5f620-88ed-57a1-8526-b8b10e192d7a
-- title:
--   FHS: mixed1
-- statement:
--   The FHS construction uses the mixed1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L104-L114

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

theorem PI.FHS.mixed1 {Z : Mat p q} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by sorry
