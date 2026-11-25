-- Prove2me | Theorems.Thm_PI_FHS_fockInner_self_eq_zero
-- name    : PI.FHS.fockInner_self_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:15.066654+00:00
-- url     : https://prove2.me/theorems/b10bdccc-233d-4e27-b91e-8af883c2732d
-- title:
--   FHS: fock Inner self eq zero
-- statement:
--   The FHS construction uses the fock Inner self eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L147-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L147-L160

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

theorem PI.FHS.fockInner_self_eq_zero {P : MvPolynomial σ ℂ} (h : FockH1Action.fockInner P P = 0) : P = 0 := by sorry
