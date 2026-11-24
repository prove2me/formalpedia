-- Prove2me | Theorems.Thm_PI_FHS_fockInner_add_left
-- name    : PI.FHS.fockInner_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:03.05334+00:00
-- url     : https://prove2.me/theorems/7b2c18b6-a484-4ff2-b4cf-afcd5c9a4822
-- title:
--   FHS: fock Inner add left
-- statement:
--   The FHS construction uses the fock Inner add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L67-L75

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

theorem PI.FHS.fockInner_add_left (P P' Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P + P') Q = FockH1Action.fockInner P Q + FockH1Action.fockInner P' Q := by sorry
