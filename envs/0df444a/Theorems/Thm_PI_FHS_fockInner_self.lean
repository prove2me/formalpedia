-- Prove2me | Theorems.Thm_PI_FHS_fockInner_self
-- name    : PI.FHS.fockInner_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:57.151786+00:00
-- url     : https://prove2.me/theorems/4237b436-4365-4753-8743-70736ac0bb76
-- title:
--   FHS: fock Inner self
-- statement:
--   The FHS construction uses the fock Inner self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L133-L139

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

theorem PI.FHS.fockInner_self (P : MvPolynomial σ ℂ) : FockH1Action.fockInner P P =
    ∑ α ∈ P.support, (((Complex.normSq (coeff α P)) *
      ((α.prod fun _ k => k.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by sorry
