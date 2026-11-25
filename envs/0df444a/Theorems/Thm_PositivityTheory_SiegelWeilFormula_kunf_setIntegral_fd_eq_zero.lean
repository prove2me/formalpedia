-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_setIntegral_fd_eq_zero
-- name    : PositivityTheory.SiegelWeilFormula.kunf.setIntegral_fd_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:03:32.21155+00:00
-- url     : https://prove2.me/theorems/b2e82432-a6d2-5be6-b8ac-8da35baf527d
-- title:
--   kunf: set Integral fd eq zero
-- statement:
--   The kunf construction uses the set Integral fd eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfA.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfA.lean#L35-L50

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}
omit [SecondCountableTopology V]

theorem PositivityTheory.SiegelWeilFormula.kunf.setIntegral_fd_eq_zero (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (g : V → ℂ)
    (hg : ∀ (ν : Λ) β, g (β + ν) = g β) (β₀ : V) (c : ℂ) (hc : c ≠ 1) (hβ₀ : ∀ β, g (β + β₀) = c * g β) :
    ∫ β in 𝓖, g β ∂lam = 0 := by sorry
