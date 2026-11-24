-- Prove2me | Theorems.Thm_PI_FHS_fockInner_X_mul
-- name    : PI.FHS.fockInner_X_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:36.692101+00:00
-- url     : https://prove2.me/theorems/8a37b4fa-4e29-4c9f-acf8-128d277d8e5d
-- title:
--   FHS: fock Inner X mul
-- statement:
--   The FHS construction uses the fock Inner X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L202-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L202-L227

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

theorem PI.FHS.fockInner_X_mul [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q) := by sorry
