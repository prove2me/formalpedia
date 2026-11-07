-- Prove2me | Theorems.Thm_PathCount2k_theorem_1_1
-- name    : PathCount2k.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:47.545352+00:00
-- url     : https://prove2.me/theorems/08bcb438-91e4-45a1-b22d-21de922c24d5
-- title:
--   Theorem 1.1 — $k$-vertex paths counted to $1\pm\varepsilon$ w.p. $1-\delta$ in $2^kk^{O(1)}(n+m)\varepsilon^{-2}\log(2/\delta)$ operations
-- statement:
--   Let $G$ be a directed graph with $n$ vertices and $m$ arcs, $k\ge1$ an integer and $0<\varepsilon,\delta<1$, and let $N$ be the number of directed $k$-vertex paths in $G$. The randomized algorithm of §2.12 (`countPaths`), run on a tape of $L$ fair random bits ($L=4TJ$ when $2\le k\le n$, $L=0$ otherwise), returns an estimate $\hat N$ with
--   $$
--   \Pr\big[|\hat N-N|\le\varepsilon N\big]\ge1-\delta,
--   $$
--   the probability being over the $2^L$ tapes, and on every tape it uses at most
--   $$
--   C\cdot2^k\cdot k^c\cdot(n+m+1)\cdot\varepsilon^{-2}\log(2/\delta)
--   $$
--   arithmetic operations, where $C$ and $c$ are universal constants.
--
--   This is the first approximation scheme for counting $k$-paths with exponential base $2$, resolving a question of Koutis and Williams.
--
--   Differences from the source:
--
--   - reading: there is a randomized algorithm … using … arithmetic operations → the paper's §2.12 algorithm written as the program countPaths in the arithmetic-operation model (cost monad CapacitatedAssort.General.Work: every arithmetic operation and comparison on a numeric value charged); each sampler draw is charged one operation and its bits are counted by the tape length; the median is a linear-time selection; the parameters R, q, T, J, Γ are computed by charged loops; reason: without the program the existence claim holds by exact brute-force counting; this is the paper's accounting (§2.11, proof of Thm 1.1, Lemma 2.15)
--   - reading: 2^k k^{O(1)}(n + m)ε⁻² log(2/δ) → ∃ universal C, c : ℕ, quantified before n, E, k, ε, δ, with ops ≤ C·2^k·k^c·(n + m + 1)·ε⁻²·log(2/δ) on every tape; reason: the meaning of k^{O(1)}; natural log, the base only changes C
--   - encoding: a directed graph with n vertices and m arcs; positions 1, …, k; fair random bits; ξ from accepted 4-bit values; n + m → vertices Fin n, arcs a list A without repetitions (E = A.toFinset, m = |A|), positions Fin k, a uniform tape Fin L → Bool with L = bitBudget n k ε δ, the decoding table 0–5 ↦ 0, 6–7 ↦ 1, 8–9 ↦ −1, 10 ↦ 2, 11 ↦ −2, the factor n + m + 1; reason: same instances: every arc set is A.toFinset of such a list; n + m + 1 ≤ 2(n + m) when n ≥ 1, and at n = 0 the printed bound is 0 while the program still compares k with n
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Theorem 1.1, p.2; algorithm §2.12, p.17; proof pp.17–18

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_DP
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_Algorithm

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Theorem 1.1** (Counting paths), p.2: "Given a directed graph `G` with `n` vertices
and `m` arcs, an integer `k ≥ 1`, and `0 < ε, δ < 1`, there is a randomized algorithm that returns
an estimate `N̂` of the number `N` of directed `k`-vertex paths in `G` satisfying
`Pr[|N̂ − N| ≤ εN] ≥ 1 − δ`, using `2^k k^{O(1)}(n + m)ε⁻² log(2/δ)` arithmetic operations."

The algorithm is the paper's §2.12 algorithm, the charged program `countPaths`, run on a tape of
`L = bitBudget n k ε δ` fair random bits (`4TJ` when `2 ≤ k ≤ n`, Lemma 2.15). There are universal
constants `C, c` such that for every `n`, every arc set given as a list `A` without repetitions
(`m = |A|`), every `k ≥ 1` and every `0 < ε, δ < 1`:
1. among the `2^L` tapes, the fraction on which the output `N̂` satisfies `|N̂ − N| ≤ εN` is at
   least `1 − δ`;
2. on **every** tape the number of charged arithmetic operations is at most
   `C · 2^k · k^c · (n + m + 1) · ε⁻² · log(2/δ)`.

**Formalization Note.** "There is a randomized algorithm … using … arithmetic operations" is read as
a statement about the paper's own algorithm, written out as `countPaths` in the cost monad
`CapacitatedAssort.General.Work`; without the program the existence claim would be trivial. Each
scalar draw of the sampler is charged one operation (its bits are counted by the tape length),
the median is a linear-time selection, the parameters are computed by charged loops. `log` is the
natural logarithm; `n + m + 1` reads `n + m`. `C, c` are quantified before every datum. -/
theorem theorem_1_1 :
    ∃ C c : ℕ, ∀ (n : ℕ) (A : List (Fin n × Fin n)), A.Nodup → ∀ k : ℕ, 1 ≤ k →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (((Finset.univ.filter fun b : Fin (bitBudget n k ε δ) → Bool =>
            |((countPaths n A k ε δ b).run 0).1 - (N n A.toFinset k : ℝ)| ≤
              ε * (N n A.toFinset k : ℝ)).card : ℝ) / 2 ^ bitBudget n k ε δ ≥ 1 - δ) ∧
          ∀ b : Fin (bitBudget n k ε δ) → Bool,
            ((((countPaths n A k ε δ b).run 0).2 : ℕ) : ℝ) ≤
              (C : ℝ) * 2 ^ k * (k : ℝ) ^ c * ((n : ℝ) + A.length + 1) * ε ^ (-2 : ℤ) *
                Real.log (2 / δ) := by sorry

end PathCount2k
