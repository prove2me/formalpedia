-- Prove2me | Theorems.Thm_PI_FHS_fockInner_eq_sum_right
-- name    : PI.FHS.fockInner_eq_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:16.18673+00:00
-- url     : https://prove2.me/theorems/cb3d9b2f-49d8-42cb-8390-6346ab095f1b
-- title:
--   FHS: fock Inner eq sum right
-- statement:
--   The FHS construction uses the fock Inner eq sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L62-L65

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

theorem PI.FHS.fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    FockH1Action.fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by sorry
