-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_5_2
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:49:46.638791+00:00
-- url     : https://prove2.me/theorems/19eccae5-5137-4183-9903-2bd692837f2a
-- title:
--   Theorem 5.2 — Feasible polynomial-time half-competitive Algorithm 8 and optimality
-- statement:
--   Algorithm 8 produces a feasible divisible allocation for every valid sample/real profile. Under every fixed adversarial real arrival order it is exactly $1/2$-competitive in GoG, with a uniform polynomial bound on primitive operations. No family of randomized online algorithms, even with unrestricted computation, can guarantee any uniform ratio $1/2+\epsilon$ for $\epsilon>0$ across all finite buyer sizes.
--   $$\mathbb E[\mathrm{Alg}_8(s,r)]\ge\tfrac12\mathbb E[\mathrm{Opt}(r)].$$
--   Original demands may be zero or fractional, densities may vanish or tie, and real pairs need not be independent draws.
--
--   Differences from the source:
--   - encoding: Algorithm 8 with the expressly permitted random infinitesimal tie perturbation and dummy fill → strict lexicographic density/rank comparison with symmetric distinct ranks, a unit zero-density sample dummy, and original-density rewards; reason: the one-buyer equal-density example would fail under the unqualified strict density-only rule; the source explicitly allows this tie convention and zero dummy, so no input is excluded
--   - encoding: polynomial-time positive result and best possible ratio over all algorithms → one uniform polynomial for the concrete sort/scan, plus a quantified unrestricted family upper bound over finite sizes; reason: cost counts the actual sorting and prefix scans; the impossibility is not asserted separately for each fixed size
--   - encoding: expectations over the specified independent random choices → explicit fair finite GoG averages and nonnegative expectations over independent algorithm seeds; reason: these are ordinary expectations for measurable source payoffs; no input distribution or finite-support restriction is imposed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 5.2, printed p. 27 / PDF p. 29; proof printed 28–30 / PDF 30–32.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 5.2, PDF 29 / printed 27. Operational Algorithm 8, feasibility,
exact half, polynomial operations, and the unrestricted uniform upper bound. -/
theorem theorem_5_2 :
    (∃ K : ℕ, ∀ n : ℕ, (alg8 n).Valid ∧
      (∀ ρ, (alg8 n).Competitive (1/2) ρ) ∧
      ∀ ω s ρ r, (∀ t i, ItemValid .divisible (s t i)) →
        (∀ i, ItemValid .divisible (r i)) →
        spiCost (alg8 n) ω s ρ r ≤ K*(n+1)^K) ∧
    ∀ ε : ℝ, 0 < ε → ∀ S : (n : ℕ) → KSPI .divisible n 1,
      (∀ n, (S n).Valid) → ∃ n, ∃ ρ : Equiv.Perm (Fin n),
        ¬ (S n).Competitive (1/2+ε) ρ := by sorry

end SingleSampleCombPI.XOS.Supplement
