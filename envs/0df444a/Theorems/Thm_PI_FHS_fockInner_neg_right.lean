-- Prove2me | Theorems.Thm_PI_FHS_fockInner_neg_right
-- name    : PI.FHS.fockInner_neg_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:42.506661+00:00
-- url     : https://prove2.me/theorems/4652b692-05e7-4203-80d2-25f5c45a02e0
-- title:
--   FHS: fock Inner neg right
-- statement:
--   The FHS construction uses the fock Inner neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L100-L105

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

theorem PI.FHS.fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = - FockH1Action.fockInner P Q := by sorry
