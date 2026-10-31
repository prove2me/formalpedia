-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_4_c4
-- name    : PersuasionNetworks.lemma_4_c4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:22.476838+00:00
-- url     : https://prove2.me/theorems/2c22b4b5-c8e0-48f0-8881-51e835a46fb0
-- title:
--   Proof of Lemma 4, "Proof C4 holds" — a C1–C3 solution can be improved to satisfy C4
-- statement:
--   For every feasible solution of (OPT) that satisfies C1, C2 and C3 there is a feasible solution that satisfies C1–C4, with a weakly larger objective value.
--
--   This is the last step of the proof of Lemma 4. C4 is what later makes the two equations of Algorithm 1 solvable.
--
--   Differences from the source: none.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Proof of Lemma 4, "Proof C4 holds", pp.47–48

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Proof of Lemma 4, "Proof C4 holds"**, Candogan, SSRN 3346144 (preprint), pp.47–48. Given a feasible solution that
satisfies C1–C3, another feasible solution with weakly larger objective value which satisfies C4
(in addition to C1–C3) can be obtained. -/
theorem lemma_4_c4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z)
    (hC1 : C1 μ 𝒯 K p z) (hC2 : C2 K p z) (hC3 : C3 μ 𝒯 K p z) :
    ∃ p' z', IsFeasible μ 𝒯 K b p' z' ∧ SatisfiesC μ 𝒯 K p' z' ∧
      objective K r p ≤ objective K r p' := by sorry

end PersuasionNetworks
