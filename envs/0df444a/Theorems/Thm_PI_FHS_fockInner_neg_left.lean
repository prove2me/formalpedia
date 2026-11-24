-- Prove2me | Theorems.Thm_PI_FHS_fockInner_neg_left
-- name    : PI.FHS.fockInner_neg_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:39.281203+00:00
-- url     : https://prove2.me/theorems/b95a2dc6-0f3e-4488-a712-80b21943959c
-- title:
--   FHS: fock Inner neg left
-- statement:
--   The FHS construction uses the fock Inner neg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L107-L114

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

theorem PI.FHS.fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (-P) Q = - FockH1Action.fockInner P Q := by sorry
