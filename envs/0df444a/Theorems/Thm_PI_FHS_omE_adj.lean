-- Prove2me | Theorems.Thm_PI_FHS_omE_adj
-- name    : PI.FHS.omE_adj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:42.631259+00:00
-- url     : https://prove2.me/theorems/797aa62f-40e5-41b8-8b77-d415459934c4
-- title:
--   FHS: om E adj
-- statement:
--   The FHS construction uses the om E adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/ConjTransposeOneKronecker.lean#L55-L65

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

theorem PI.FHS.omE_adj {l l' : Ln p q r s} (h : linePos l ≠ linePos l') (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = - fockInner P (omE l' l Q) := by sorry
