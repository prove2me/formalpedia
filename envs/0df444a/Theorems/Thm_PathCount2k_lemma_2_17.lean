-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_17
-- name    : PathCount2k.lemma_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:44:19.957808+00:00
-- url     : https://prove2.me/theorems/42ed685e-73fd-4a9b-9c80-966c6d81156d
-- title:
--   Lemma 2.17 — one trial costs $2^k k^{O(1)}(n+m)$ arithmetic operations
-- statement:
--   There are universal constants $C,c$ such that, for every graph with $n$ vertices given by a list of $m$ arcs, every $k\ge1$, $D=k$, and every choice of the integer samples, the dynamic program of §2.10, including its output step $(zb_0)^2/(k!D^{k-1})$, performs at most
--   $$
--   C\cdot2^k\cdot k^c\cdot(n+m+1)
--   $$
--   arithmetic operations.
--
--   Each layer touches $\binom kp$ rows per vertex and per arc, and $\sum_p\binom kp=2^k$; this is where the base $2$ of Theorem 1.1 comes from.
--
--   Differences from the source:
--
--   - reading: 2^k k^{O(1)}(n + m) arithmetic operations → ∃ universal C, c : ℕ, quantified before every datum, with charged count ≤ C·2^k·k^c·(n + m + 1); reason: the meaning of k^{O(1)}; n + m + 1 ≤ 2(n + m) when n ≥ 1, and the printed bound is 0 at n = 0, where the program still enumerates masks
--   - generalization: 2 ≤ k ≤ n (assumed in §2.11, p.16) → every k ≥ 1 and every n; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - encoding: arithmetic operations on scalar values at unit cost → the operation count of the program dpOutput (dp followed by the squaring and the normalization by k!·D^{k−1}) in the cost monad Work (every arithmetic operation on a table value charged; mask and sign bookkeeping charged too); the graph as an arc list of length m; reason: the paper's unit; extra bookkeeping charges only make the count larger
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.17, p.16

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_DP

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.17** (Arithmetic complexity), p.16: "Given the vectors and matrices,
the dynamic program evaluates `Y₀` using `2^k k^{O(1)}(n + m)` arithmetic operations", with `D = k`
(§2.11, p.16).

There are universal constants `C, c` such that, for every graph given by an arc list `A` of
length `m`, every `k ≥ 1` and every choice of the integer samples, the charged operation count of
the dynamic program `dpOutput` (§2.10 steps 1–3, including the output `(z b₀)²/(k! D^{k−1})`) is at
most `C · 2^k · k^c · (n + m + 1)`.

**Formalization Note.** The count is the state of the cost monad after `dpOutput`; the charges are
listed in `Definitions.Def_PathCount2k_DP` (every arithmetic operation on a table value, plus mask
and sign bookkeeping). `C, c` are quantified before every datum; `n + m + 1` reads the paper's
`n + m` (equal up to a factor 2 when `n ≥ 1`). The count includes the final squaring and
normalization ("Initialization, the final summation, and normalization are also covered by this
bound", p.16). Stated for every
`k ≥ 1` (the paper assumes `2 ≤ k ≤ n`, §2.11). -/
theorem lemma_2_17 :
    ∃ C c : ℕ, ∀ (n : ℕ) (A : List (Fin n × Fin n)) (k : ℕ), 1 ≤ k →
      ∀ (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin k → Fin k → ℤ),
        ((dpOutput n k k A g H).run 0).2 ≤ C * 2 ^ k * k ^ c * (n + A.length + 1) := by sorry

end PathCount2k
