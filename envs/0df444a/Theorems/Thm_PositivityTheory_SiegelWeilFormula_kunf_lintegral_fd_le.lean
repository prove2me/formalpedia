-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_kunf_lintegral_fd_le
-- name    : PositivityTheory.SiegelWeilFormula.kunf.lintegral_fd_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:15.166269+00:00
-- url     : https://prove2.me/theorems/0a90cbc1-a269-4fad-93ec-4b015592f078
-- title:
--   kunf: lintegral fd le
-- statement:
--   The kunf construction uses the lintegral fd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfA.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/UnfoldingCompactness/AbsUnfA.lean#L16-L31

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

theorem PositivityTheory.SiegelWeilFormula.kunf.lintegral_fd_le (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (S : V → ℝ≥0∞)
    (hS : ∀ (ν : Λ) β, S (β + ν) = S β) {C : Set V} (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C) :
    ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := by sorry
