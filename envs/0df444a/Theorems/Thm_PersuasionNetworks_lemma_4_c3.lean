-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_4_c3
-- name    : PersuasionNetworks.lemma_4_c3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:38.943476+00:00
-- url     : https://prove2.me/theorems/543e6bbb-4993-4c42-96dd-51ced8b1b53e
-- title:
--   Proof of Lemma 4, "Proof C3 holds" — a C1–C2 solution can be improved to satisfy C3
-- statement:
--   For every feasible solution of (OPT) that satisfies C1 and C2 there is a feasible solution that satisfies C1, C2 and C3, that is, $|\bar L_i\cap P|\le2$ for all $i$, with a weakly larger objective value.
--
--   This is the third step of the proof of Lemma 4, and the source of the double-interval structure.
--
--   Differences from the source: none.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Proof of Lemma 4, "Proof C3 holds", pp.43–46

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Proof of Lemma 4, "Proof C3 holds"**, Candogan, SSRN 3346144 (preprint), pp.43–46. Starting with a feasible solution
that satisfies C1 and C2, another feasible solution that satisfies C3 in addition to C1 and C2 and
yields a weakly larger objective value can be constructed. -/
theorem lemma_4_c3 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z) (hC1 : C1 μ 𝒯 K p z) (hC2 : C2 K p z) :
    ∃ p' z', IsFeasible μ 𝒯 K b p' z' ∧ C1 μ 𝒯 K p' z' ∧ C2 K p' z' ∧ C3 μ 𝒯 K p' z' ∧
      objective K r p ≤ objective K r p' := by sorry

end PersuasionNetworks
