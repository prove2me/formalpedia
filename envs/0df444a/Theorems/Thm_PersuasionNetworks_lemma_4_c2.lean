-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_4_c2
-- name    : PersuasionNetworks.lemma_4_c2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:07.099733+00:00
-- url     : https://prove2.me/theorems/588dfed5-fee9-484f-b44d-ab6bc526be8c
-- title:
--   Proof of Lemma 4, "Proof C2 holds" — a C1 solution can be made to satisfy C2
-- statement:
--   For every feasible solution of (OPT) that satisfies C1 there is a feasible solution that satisfies C1 and C2, that is, $z_k=0$ whenever $p_k=0$, and that has the same objective value.
--
--   This is the second of the four steps of the proof of Lemma 4.
--
--   Differences from the source: none.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Proof of Lemma 4, "Proof C2 holds", pp.42–43

import Mathlib
import Definitions.Def_PersuasionNetworks_OPT
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Proof of Lemma 4, "Proof C2 holds"**, Candogan, SSRN 3346144 (preprint), pp.42–43. Starting with a feasible solution
that satisfies C1, a feasible solution that satisfies C1 and C2 and yields the same objective value
can be achieved. -/
theorem lemma_4_c2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (p z : ℕ → ℝ) (hfeas : IsFeasible μ 𝒯 K b p z) (hC1 : C1 μ 𝒯 K p z) :
    ∃ p' z', IsFeasible μ 𝒯 K b p' z' ∧ C1 μ 𝒯 K p' z' ∧ C2 K p' z' ∧
      objective K r p' = objective K r p := by sorry

end PersuasionNetworks
