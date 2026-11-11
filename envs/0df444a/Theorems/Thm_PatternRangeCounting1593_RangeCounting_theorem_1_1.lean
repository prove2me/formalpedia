-- Prove2me | Theorems.Thm_PatternRangeCounting1593_RangeCounting_theorem_1_1
-- name    : PatternRangeCounting1593.RangeCounting.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:17.164741+00:00
-- url     : https://prove2.me/theorems/a4b74871-1660-41ce-8ab3-75df2835e5e0
-- title:
--   Theorem 1.1 — pattern-avoiding range counting in constant time and 2n log s_π + o(n) bits
-- statement:
--   There is an absolute constant $T$ with the following property. Fix any permutation pattern $\pi$ and a width parameter $K\ge2$. There are fixed programs (a constructor, a dominance query and a rectangle query, depending only on $\pi$ and $K$), constants $A,C,T_0,n_0$ and, for the case $|\pi|\ge3$, retained Kozma–Opler operation programs and functions $e\ge0$, $r$ with $e(n)/n\to0$ and $r(n)/n\to0$, such that for every $n$, every $\pi$-avoiding permutation $\tau$ of length $n$ and every admissible word size $w$ the constructor, started on the explicit permutation, produces a bit string $\beta_\tau$ and:
--
--   1. **construction:** it halts within $A n+A$ steps using at most $A n+A$ working words;
--   2. **space:** $|\beta_\tau|\le Cn+C$;
--   3. **dominance:** for all $0\le x,y\le n$ the dominance query, given only the packed $\beta_\tau$, $n$, $|\beta_\tau|$ and $(x,y)$, returns $\mathrm{Count}_\tau(x,y)$ within $T_0$ steps, and within $T$ steps when $n\ge n_0$;
--   4. **rectangles:** for all $0\le x_1,x_2,y_1,y_2\le n$ the rectangle query returns $|P_\tau\cap([x_1,x_2]\times[y_1,y_2])|$ within $T_0$ steps, and within $T$ steps when $n\ge n_0$;
--   5. **succinctness for $|\pi|\ge3$:**
--   $$|\beta_\tau|\le 2n\log_2 s_\pi+r(n),$$
--   and $\beta_\tau=\beta^{KO}\,\iota$ with $|\iota|\le e(n)$, where for $n\ge n_0$ the prefix $\beta^{KO}$ is a retained Kozma–Opler representation of $\tau$.
--
--   The same representation supports both query types. For $|\pi|\le2$ the avoidance class has at most one member of each length, and the empty pattern has no avoiders.
--
--   This resolves the question of Kozma and Opler whether exact counting on pattern-avoiding permutations can take constant time; their structure answers in $O(\log\log n)$ time within the same space.
--
--   **Formalization Note** $O_\pi(n)$ bits, time and words are $Cn+C$ and $An+A$ with constants depending on $\pi$ and $K$; $o_\pi(n)$ is a function divided by $n$ tending to $0$, uniform over all avoiders; the query constant $T$ is quantified before $\pi$. The query receives no copy of $\tau$.
--
--   Differences from the source:
--   - generalization: deterministic word RAM with w = Θ(log N) and constant-time standard operations including multiplication and most-significant-bit → the explicit instruction set of Def_Machine (one step per instruction, no division) at every width 2·b(N) ≤ w ≤ K·b(N) for a fixed K ≥ 2, N = max{2, n}; reason: uniformity over each fixed bounded width band; choosing K = 2 and w = 2·b(max{2,n}) recovers one legal logarithmic width rule sufficient for coordinate pairs, so every source instance is covered
--   - reading: O(1) worst-case queries → an absolute constant T (before π and K) for n ≥ n₀(π, K), and a constant T₀(π, K) for every n; reason: §3.1: for each fixed parameter choice the query takes an absolute constant number of word operations on sufficiently large inputs; smaller inputs are handled by direct lookup
--   - reading: the additional index uses o_π(n) bits beyond the retained Kozma–Opler representation → the bit string is base ++ idx with |idx| ≤ e(n), e(n)/n → 0, and base satisfies the retained interface of Def_KOInterface (K1)–(K4) for n ≥ n₀; base itself has fewer than 2^w bits; reason: Kozma–Opler's encoding is external; its content used by the paper is the interface of Theorem 3.4; the base must be inside the operation contract domain
--   - encoding: an O_π(n)-bit representation; O_π(n) time and working words → a packed bit string of length ≤ C·n + C produced by a construction run of ≤ A·n + A steps and working words; reason: explicit constants depending on π and K
--   - encoding: query input: the representation and the cutoffs → registers n, |bits|, the cutoffs; memory the packed bits only; reason: n and the length are O(log n)-bit metadata
--   - encoding: exact dominance and arbitrary rectangle counting queries → Count_τ(x, y) for 0 ≤ x, y ≤ n and inclusive rectangles with 0 ≤ x₁, x₂, y₁, y₂ ≤ n (empty intervals allowed); reason: cutoff domain [0, n] of §1.1
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), Theorem 1.1, printed p. 1 (PDF p. 2); proof in §5 (printed p. 21, PDF p. 22) and §7.1

import Mathlib
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Perm
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
import Definitions.Def_PatternRangeCounting1593_RangeCounting_Hierarchy
import Definitions.Def_PatternRangeCounting1593_RangeCounting_KOInterface
import Definitions.Def_PatternRangeCounting1593_RangeCounting_IndexSpecs
set_option autoImplicit false
open Filter Topology
open Classical

namespace PatternRangeCounting1593.RangeCounting

/-- Theorem 1.1 (Pattern-avoiding range counting). -/
theorem theorem_1_1 :
    ∃ T : ℕ, ∀ (k : ℕ) (π : Equiv.Perm (Fin k)) (K : ℕ), 2 ≤ K →
      ∃ (build domQ rectQ : Program) (A C T₀ n₀ : ℕ) (P : KOProgs) (Tko cKO : ℕ)
        (e r : ℕ → ℝ),
        (∀ n, 0 ≤ e n) ∧
        Tendsto (fun n : ℕ => e n / n) atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => r n / n) atTop (𝓝 0) ∧
        ∀ n : ℕ, ∀ τ : Equiv.Perm (Fin n), Avoids π τ → ∀ w, WidthOK K n w →
          ∃ bits : List Bool,
            BuildsWith w build (permMem τ) [n] ((A * n + A : ℕ) : ℝ) ((A * n + A : ℕ) : ℝ)
              bits [] ∧
            bits.length ≤ C * n + C ∧
            (∀ x y, x ≤ n → y ≤ n →
              RunsQuery w domQ (packBits w bits) [n, bits.length, x, y] [Count τ x y] T₀ ∧
              (n₀ ≤ n →
                RunsQuery w domQ (packBits w bits) [n, bits.length, x, y] [Count τ x y] T)) ∧
            (∀ x₁ x₂ y₁ y₂, x₁ ≤ n → x₂ ≤ n → y₁ ≤ n → y₂ ≤ n →
              RunsQuery w rectQ (packBits w bits) [n, bits.length, x₁, x₂, y₁, y₂]
                [rectCount τ x₁ x₂ y₁ y₂] T₀ ∧
              (n₀ ≤ n →
                RunsQuery w rectQ (packBits w bits) [n, bits.length, x₁, x₂, y₁, y₂]
                  [rectCount τ x₁ x₂ y₁ y₂] T)) ∧
            (3 ≤ k →
              (bits.length : ℝ) ≤ 2 * n * Real.logb 2 (swLimit π) + r n ∧
              ∃ base idx : List Bool, bits = base ++ idx ∧ (idx.length : ℝ) ≤ e n ∧
                (n₀ ≤ n → ∃ (Hd : Hierarchy) (hdl : Handles),
                  KOInterface π w τ P Tko cKO base Hd hdl)) := by sorry

end PatternRangeCounting1593.RangeCounting
