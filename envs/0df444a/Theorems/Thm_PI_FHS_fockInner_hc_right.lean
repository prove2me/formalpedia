-- Prove2me | Theorems.Thm_PI_FHS_fockInner_hc_right
-- name    : PI.FHS.fockInner_hc_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:20.116855+00:00
-- url     : https://prove2.me/theorems/dd92c9ea-5571-5945-a158-832a9d2188ed
-- title:
--   FHS: fock Inner hc right
-- statement:
--   The FHS construction uses the fock Inner hc right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L249-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L249-L261

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

theorem PI.FHS.fockInner_hc_right {n : ℕ} (P Q : MvPolynomial σ ℂ) (hP : P ∈ FockH1Action.homog σ n) :
    FockH1Action.fockInner P (homogeneousComponent n Q) = FockH1Action.fockInner P Q := by sorry
