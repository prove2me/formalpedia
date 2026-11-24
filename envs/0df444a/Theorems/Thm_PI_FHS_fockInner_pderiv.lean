-- Prove2me | Theorems.Thm_PI_FHS_fockInner_pderiv
-- name    : PI.FHS.fockInner_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:47.356806+00:00
-- url     : https://prove2.me/theorems/83340be7-add2-407c-8d23-eb98e334374e
-- title:
--   FHS: fock Inner pderiv
-- statement:
--   The FHS construction uses the fock Inner pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L229-L231

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

theorem PI.FHS.fockInner_pderiv [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (pderiv l P) Q = FockH1Action.fockInner P (X l * Q) := by sorry
