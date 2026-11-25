-- Prove2me | Theorems.Thm_PositivityTheory_ThK_SplitLoc_Unr_zetaUnr_eq_integral
-- name    : PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_eq_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:20.954189+00:00
-- url     : https://prove2.me/theorems/c7f05cac-0355-4227-a6e2-756bbce17f55
-- title:
--   Unr: zeta Unr eq integral
-- statement:
--   The Unr construction uses the zeta Unr eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L897-L950
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/UpperProjectionInverseTransposeRightInverse.lean#L897-L950

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SplitLoc
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyDeepSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_UpperProjectionInverseTransposeRightInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem PositivityTheory.ThK.SplitLoc.Unr.zetaUnr_eq_integral {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (hu : ‖(ν ϖ : ℂ)‖ = 1)
    {n d : ℕ} (hn : 2 * n < d + 2) {φ : Matrix (Fin n) (Fin n) k → ℂ} (hφ : φ ∈ SB _) :
    Integrable (fun g : GL (Fin n) k => φ g.val * wt d ν g) (haarVol (KO k (Fin n))) ∧
      (invL n d ϖ ν).eval 1 * ∫ g, φ g.val * wt d ν g ∂haarVol (KO k (Fin n)) = zetaUnr n d ϖ ν φ := by sorry
