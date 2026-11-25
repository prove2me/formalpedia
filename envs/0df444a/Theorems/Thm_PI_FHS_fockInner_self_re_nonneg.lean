-- Prove2me | Theorems.Thm_PI_FHS_fockInner_self_re_nonneg
-- name    : PI.FHS.fockInner_self_re_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:25.203995+00:00
-- url     : https://prove2.me/theorems/002117f9-7e5e-4f0d-9e8a-11b149221512
-- title:
--   FHS: fock Inner self re nonneg
-- statement:
--   The FHS construction uses the fock Inner self re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L141-L145

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}

theorem PI.FHS.fockInner_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (FockH1Action.fockInner P P).re := by sorry
