-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_4_c1
-- name    : PersuasionNetworks.lemma_4_c1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:16.570271+00:00
-- url     : https://prove2.me/theorems/284fb706-c110-40fc-9350-f678ea811dd9
-- title:
--   Proof of Lemma 4, "Proof C1 holds" — a feasible solution can be made to satisfy C1
-- statement:
--   For every feasible solution of (OPT) there is a feasible solution that satisfies C1, that is, the first constraint binds at $L=\mathcal S$, and that has the same objective value.
--
--   This is the first of the four steps of the proof of Lemma 4.
--
--   Differences from the source: none.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Proof of Lemma 4, "Proof C1 holds", p.42

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Proof of Lemma 4, "Proof C1 holds"**, Candogan, SSRN 3346144 (preprint), p.42. Starting with a feasible solution to
(OPT), another feasible solution that satisfies C1 and yields the same objective value can be
obtained. -/
theorem lemma_4_c1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z) :
    ∃ p' z', IsFeasible μ 𝒯 K b p' z' ∧ C1 μ 𝒯 K p' z' ∧ objective K r p' = objective K r p := by sorry

end PersuasionNetworks
