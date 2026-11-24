-- Prove2me | Theorems.Thm_PI_FHS_fockInner_zero_left
-- name    : PI.FHS.fockInner_zero_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:42.899965+00:00
-- url     : https://prove2.me/theorems/6e1aa5e9-76b5-4c06-bdd2-c47f010c38ac
-- title:
--   FHS: fock Inner zero left
-- statement:
--   The FHS construction uses the fock Inner zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L116-L117

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

theorem PI.FHS.fockInner_zero_left (Q : MvPolynomial σ ℂ) : FockH1Action.fockInner 0 Q = 0 := by sorry
