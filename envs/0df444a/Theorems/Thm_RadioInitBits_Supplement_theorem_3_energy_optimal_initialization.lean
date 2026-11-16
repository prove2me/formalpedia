-- Prove2me | Theorems.Thm_RadioInitBits_Supplement_theorem_3_energy_optimal_initialization
-- name    : RadioInitBits.Supplement.theorem_3_energy_optimal_initialization
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:05:42.109206+00:00
-- url     : https://prove2.me/theorems/e7b31d7c-48cd-445d-ae03-97aeb98a8e1f
-- title:
--   Theorem 3 — with $O(\log n)$-bit messages and no collision detection, $(1-f)$-initialization w.p. $\ge 1-1/n^2$ in $O(n)$ rounds with energy $O(\log\log(1/f))$
-- statement:
--   In the **no-CD model with $O(\log n)$-bit messages**, $(1-f)$-initialization can be solved with energy depending only on $f$.
--
--   Precisely, there are a family of anonymous randomized protocols $P_{n,f}$ (run on $n$ nodes that all know $n$ and $f$) and an absolute constant $C$ such that for every $n\ge 3$ and every $f\in(0,1]$:
--
--   1. every message transmitted in every execution of $P_{n,f}$ has at most $C\log n$ bits;
--   2. $P_{n,f}$ runs for at most $Cn$ rounds;
--   3. in every execution, every node transmits or listens in at most $C\max\{1,\log\log(1/f)\}$ rounds;
--   4. over the nodes' independent private seeds,
--   $$\Pr\big[\text{the execution does not solve }(1-f)\text{-initialization}\big]\ \le\ \frac1{n^2}.$$
--
--   So a constant fraction of the nodes can be initialized with constant energy, and full initialization ($f<1/n$) costs $O(\log\log n)$ energy, in the model without collision detection.
--
--   **Formalization Note** Stated in the supplement's multi-bit model `RadioInitBits.Supplement.MProtocol`, with the published seeds and seed law. $C$ does not depend on $f$; the protocol may (Algorithm 1 takes $f$ as input). Logarithms are natural.
--
--   Differences from the source:
--   - encoding: O(·) bounds on message size, rounds and energy → one absolute constant C chosen before n and f, for all n ≥ 3 and all f ∈ (0, 1]; reason: the standard reading of O(·) uniform in f; finitely many small n are absorbed into C
--   - reading: energy complexity O(log log(1/f)) → energy ≤ C · max(1, log log(1/f)); reason: log log(1/f) ≤ 0 for f ≥ 1/e, and the paper's own count 2·O(log log(1/f)) + 5(1 + 15) has an additive constant; natural log, the base changes only C
--   - encoding: f ∈ [0, 1] (Definition 8) → 0 < f ≤ 1; reason: at f = 0 the bound O(log log(1/f)) is infinite and the claim is empty; Lean's log 0 = 0 would make it a different statement
--   - reading: number all but fn nodes with distinct IDs from 1 to (1 − f)n (Definition 8) → at most fn nodes output none, and the initialized nodes carry pairwise distinct IDs exactly 1, …, K with K ≥ (1 − f)n; reason: fn need not be an integer; this is what the proof delivers (at most fn nodes remain uninitialized, IDs handed out as the next available ID)
--   - reading: there exists an algorithm with round, energy and O(log n)-bit message complexity → a protocol family P n f (knowing n and f) whose rounds are fixed and whose message lengths and per-node energy are bounded in every execution; reason: complexities are maxima (p.5); Algorithm 1 takes f as input; the worst-case reading is the stronger one
--   - encoding: n identical nodes with private randomness → nodes Fin n, seeds i.i.d. uniform streams in [0, 1] (published RadioInitBits.jointSeedLaw), messages List Bool; reason: the published model of the base mission; same instances
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), short version Theorem 3, p.3 (PDF p.5); full version Theorem 3, p.3 (PDF p.24), p.16 (PDF p.37) and p.22 (PDF p.43, with proof); Definition 8, p.5 (PDF p.26)

import Mathlib
import Definitions.Def_RadioInitBits_seedLaw
import Definitions.Def_RadioInitBits_Supplement_MProtocol

set_option autoImplicit false

namespace RadioInitBits

namespace Supplement

open MeasureTheory

/-- **Theorem 3** (energy-optimal `(1 − f)`-initialization). In the no-CD model with `O(log n)`-bit
messages there is an anonymous randomized protocol that solves `(1 − f)`-initialization with
probability at least `1 − 1/n²`, with round complexity `O(n)` and energy complexity
`O(log log(1/f))`: there are a protocol family `P` (`P n f` is run on `n` nodes, all knowing `n`
and `f`) and one absolute constant `C` such that for every `n ≥ 3` and every `f ∈ (0, 1]`

1. every message transmitted in every execution of `P n f` has at most `C · log n` bits;
2. `P n f` runs for at most `C · n` rounds;
3. in **every** execution, every node transmits or listens in at most
   `C · max(1, log log(1/f))` rounds;
4. the probability over the nodes' independent private seeds that the execution does not solve
   `(1 − f)`-initialization is at most `1 / n²`.

D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), short version Theorem 3, p.3 (PDF p.5): "In the no-CD
Model with O(log n)-bit messages, there exists an algorithm that solves (1 − f)-initialization
with probability at least 1 − 1/n² and has round complexity O(n) and energy complexity
O(log log(1/f))"; full version Theorem 3, p.3 (PDF p.24), p.16 (PDF p.37) and p.22 (PDF p.43),
with "Algorithm 1" in place of "there exists an algorithm".

**Formalization Note** `O(·)` is one constant `C` chosen before `n` and `f`, for all `n ≥ 3` and
all `f ∈ (0, 1]`; the protocol may depend on `n` and `f` (Algorithm 1 takes `f` as input). `log` is
the natural logarithm (the base changes only `C`). `max(1, ·)` gives the energy bound a meaning for
`f ≥ 1/e`, where `log log(1/f) ≤ 0`; the paper's own count is `2·O(log log(1/f)) + 5(1 + 15)`.
`f = 0` is excluded: there `log log(1/f)` is infinite, and in Lean it would be the junk value `0`.
Message length, rounds and energy are bounded in every execution (worst case). -/
theorem theorem_3_energy_optimal_initialization :
    ∃ P : ℕ → ℝ → MProtocol, ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ f : ℝ, 0 < f → f ≤ 1 →
      (P n f).MsgBounded n (C * Real.log n) ∧
      ((P n f).rounds : ℝ) ≤ C * n ∧
      (∀ (ω : Fin n → Seed) (i : Fin n),
        ((P n f).energy ω i : ℝ) ≤ C * max 1 (Real.log (Real.log (1 / f)))) ∧
      jointSeedLaw n {ω | ¬ (P n f).PartialInitialized f ω} ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by sorry

end Supplement

end RadioInitBits
