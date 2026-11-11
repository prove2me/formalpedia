-- Prove2me | Theorems.Thm_PowerMinUncut_Threshold_theorem_1
-- name    : PowerMinUncut.Threshold.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:44:52.824139+00:00
-- url     : https://prove2.me/theorems/31aeec43-f82b-4cd1-9d48-cc1401bf05ee
-- title:
--   Theorem 1 — integer power rank threshold: the rank-k gap of REL_q is C_{k,q} for k > q and infinite for k ≤ q, with matching rounding and UGC hardness
-- statement:
--   Fix integers $q\ge2$ and $k\ge1$. For $k>q$ put
--   $$C_{k,q}=\frac{\Gamma((k-1+q)/2)\,\Gamma((k-q)/2)}{\Gamma((k-1)/2)\,\Gamma(k/2)}.$$
--   1. **Gap.** The supremum of $\mathrm{OPT}_{k,q}(G)/\mathrm{REL}_q(G)$ over finite rational weighted loopless graphs of positive relaxation value is $C_{k,q}$ when $k>q$, and is infinite when $k\le q$.
--   2. **Algorithm.** For every fixed $k>q$ there is a randomized Turing algorithm that, for rational $\zeta>0$ and rational $0<\omega<1$, returns exactly feasible vectors $r_i/\sqrt{r_i\cdot r_i}$, $r_i\in\mathbb Q^k\setminus\{0\}$, with cost at most $(C_{k,q}+\zeta)\,\mathrm{OPT}_{k,q}(G)$ with probability at least $1-\omega$. Running time, random-bit count and output length have deterministic polynomial bounds in the binary input length, $|V|$, $|E|$, $\max(1,1/\zeta)$ and $1+\log(1/\omega)$, with $q,k$ fixed.
--   3. **Hardness.** Assuming the Unique Games Conjecture, for each fixed $1\le A<C_{k,q}$ when $k>q$, and every fixed finite $A\ge1$ when $k\le q$, there are positive fixed thresholds $c<s$ with $s/c>A$ such that distinguishing $\mathrm{OPT}_{k,q}(G)\le c$ from $\mathrm{OPT}_{k,q}(G)\ge s$ is NP-hard.
--
--   The rank must exceed the loss power for the convex relaxation to have a bounded gap; above it the gap, the best rounding and the UGC threshold all equal $C_{k,q}$.
--
--   Differences from the source:
--   - encoding: supremum is C_{k,q}; supremum is infinite → IsLUB (gapSet k q) C_{k,q}; ¬ BddAbove (gapSet k q); reason: least upper bound of the set of ratios, not necessarily attained
--   - encoding: finite rational weighted loopless graphs (standing: weights sum to one) → gap clause over every `WGraph` with REL_q > 0; algorithm and hardness clauses over graphs of total weight one; reason: normalization preserves every ratio, so the gap set is the same set; total one is the paper's standing assumption
--   - encoding: randomized Turing algorithm with deterministic polynomial bounds → `IsRandRounding k q ι M c d`: one Cook machine and constants c, d per (k, q); coin strings of length T = ⌊c(1 + ℓ + |V| + |E| + max(1, 1/ζ) + 1 + log(1/ω))^d⌋ bound time, coins and output length on every coin string; probability = fraction of coin strings; reason: standard coin-string model; every polynomial in these quantities is bounded by such an expression
--   - encoding: Unique Games Conjecture; distinguishing … is NP-hard → `OptInapprox.MaxCut.UGC`; `PromiseNPHard k q c s` (GapNPHard with the binary graph encoding, graphs of total weight one); reason: platform definitions of UGC and gap NP-hardness
--   - generalization: positive fixed thresholds c < s → positive rational thresholds c < s; reason: rational thresholds are in particular real; Theorem 13 provides rational ones
--   - encoding: finite rational weighted loopless graph → `WGraph` on `Fin N` with a symmetric nonnegative ℚ weight function, zero diagonal; edges are pairs i < j, each counted once; reason: Lean representation; zero-weight pairs contribute nothing
-- source:
--   Xie, Sharp Power Loss Thresholds for Vector Min Uncut, STOC 2027 submission (manuscript sha256 391063da…), p. 1, §1, Theorem 1

import Mathlib
import Definitions.Def_PowerMinUncut_Threshold_Machine

open MeasureTheory ProbabilityTheory Filter Topology

namespace PowerMinUncut.Threshold

open WGraph

/-- **Theorem 1 (integer power rank threshold)**, p. 1. Fix an integer `q ≥ 2`.
* (gap) For `k > q`, the supremum of `OPT_{k,q}(G)/REL_q(G)` over finite rational weighted loopless
  graphs with `REL_q(G) > 0` is `C_{k,q}`; for `1 ≤ k ≤ q` it is infinite.
* (algorithm) For every `k > q` one randomized Turing machine, on input `(G, ζ, ω)` (weights of total
  one, rationals `ζ > 0`, `0 < ω < 1`, in binary), returns exactly feasible vectors
  `r_i/√(r_i·r_i)`, `r_i ∈ ℚ^k \ {0}`, of cost at most `(C_{k,q} + ζ) OPT_{k,q}(G)` with probability
  at least `1 - ω`; time, random bits and output length are at most
  `c(1 + ℓ + |V| + |E| + max(1, 1/ζ) + 1 + log(1/ω))^d` on every random string.
* (hardness) Assuming the Unique Games Conjecture, for every `1 ≤ A < C_{k,q}` when `k > q`, and every
  finite `A ≥ 1` when `1 ≤ k ≤ q`, there are fixed (rational) thresholds `0 < c < s` with `s/c > A`
  such that distinguishing `OPT_{k,q}(G) ≤ c` from `OPT_{k,q}(G) ≥ s` is NP-hard. -/
theorem theorem_1 (q : ℕ) (hq : 2 ≤ q) :
    (∀ k : ℕ, q < k → IsLUB (gapSet k q) (Ckp k q)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ q → ¬ BddAbove (gapSet k q)) ∧
    (∀ k : ℕ, q < k → ∃ (Γ : Type) (_ : Fintype Γ) (ι : Sym ↪ Γ) (M : CookPvsNP.TM Γ) (c d : ℕ),
      IsRandRounding k q ι M c d) ∧
    (OptInapprox.MaxCut.UGC →
      (∀ k : ℕ, q < k → ∀ A : ℝ, 1 ≤ A → A < Ckp k q →
        ∃ c s : ℚ, 0 < c ∧ c < s ∧ A < (s : ℝ) / (c : ℝ) ∧ PromiseNPHard k q c s) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ q → ∀ A : ℝ, 1 ≤ A →
        ∃ c s : ℚ, 0 < c ∧ c < s ∧ A < (s : ℝ) / (c : ℝ) ∧ PromiseNPHard k q c s)) := by sorry

end PowerMinUncut.Threshold
