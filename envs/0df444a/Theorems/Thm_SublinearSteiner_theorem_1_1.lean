-- Prove2me | Theorems.Thm_SublinearSteiner_theorem_1_1
-- name    : SublinearSteiner.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:08.52736+00:00
-- url     : https://prove2.me/theorems/b6c07c13-b22f-4264-897b-051a84b51d3f
-- title:
--   Theorem 1.1 — estimating the metric Steiner tree cost within $2-\eta_0$ in $\tilde O(n^{3/2})$
-- statement:
--   There are an absolute constant $\eta_0>0$ and a randomized algorithm that, given an $n$-point instance $(V,T,w)$ of the metric Steiner tree problem, outputs with probability at least $2/3$ a number $\widehat C$ with
--   $$\mathrm{OPT}\le\widehat C\le(2-\eta_0)\,\mathrm{OPT}.$$
--   In the worst case it makes $\tilde O(n^{3/2})$ distance queries and uses $\tilde O(n^{3/2})$ time.
--
--   The algorithm knows $V$ and $T$ and learns distances only by querying pairs. The terminal MST gives a factor-2 estimate; this theorem shows that a fixed improvement below 2 costs only $\tilde O(n^{3/2})$ queries and time.
--
--   **Formalization Note.** The algorithm is one admissible program of the distance-oracle real RAM with fair coins. $\eta_0$, the program and the constants $C,K$ of $B=\lceil Cn^{3/2}\log(n+2)^K\rceil$ are chosen before the instance. On every tape the program has halted within $B$ steps with at most $B$ units of work and $B$ queries.
--
--   Differences from the source:
--   - reading: time, on no named machine → a unit-cost real RAM with fair coins, rational literals, integer pointer addition and subtraction, a pointer-to-real cast, and no floor or real-to-integer cast; reason: the page names no machine; every omitted instruction would make a stronger machine and hence a weaker theorem
--   - encoding: Õ(n^{3/2}) → ⌈C n^{3/2} log(n+2)^K⌉ with C, K chosen before the instance; reason: §2: Õ hides fixed powers of log n; n+2 keeps the bound from collapsing at n = 1
--   - encoding: probability over the algorithm’s coins, and worst case → a count over B-bit tapes, with the halting and cost clauses on every tape; reason: a run of B steps reads at most B coins
--   - encoding: an n-point instance → n = 0 is vacuous, since IsSteinerOpt has no value without a tree; reason: the page’s n-point instance has a feasible tree; T empty, |T| = 1 and V = T are covered
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 1.1, p.1; (1.1), p.1; §2 convention for Õ, p.12

import Mathlib
import Definitions.Def_SublinearSteiner_FinMetric
import Definitions.Def_SublinearSteiner_Machine

open scoped Classical

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Theorem 1.1 (Upper bound), p.1. There is an absolute constant `η0 > 0` and a randomized algorithm that, given an `n`-point
instance, outputs with probability at least `2/3` a number `Ĉ` satisfying (1.1) with `η = η0`, that is, `OPT ≤ Ĉ ≤ (2 − η0) OPT`. In the worst
case it makes `Õ(n^{3/2})` distance queries and uses `Õ(n^{3/2})` time.

**Formalization Note.**
* The machine is the distance-oracle real RAM with fair coins of `SublinearSteiner.Machine`, the strong reading of an unnamed "time" model.
* `η0`, the program and the constants `C, K` of `Õ` come before the instance. `Õ` hides powers of `log n` (p.12), written `log(n + 2)`
  so that the bound does not collapse at `n = 1`.
* "In the worst case" is on every tape: the run has halted within `B` steps, and `work ≤ B`, `queries ≤ B`.
* The probability is the count of `B`-bit tapes over `2^B`, as a run of `B` steps reads at most `B` coins.
* For `n = 0` there is no tree, so `IsSteinerOpt` has no value and the statement is empty there. All other degenerate instances are
  covered: `T = ∅`, `|T| = 1`, `V = T`. -/
theorem theorem_1_1 :
    ∃ (η₀ : ℝ) (P : Program) (C K : ℕ), 0 < η₀ ∧ Admissible P ∧
      ∀ (n : ℕ) (T : Finset (Fin n)) (w : FinMetric n) (OPT : ℝ), IsSteinerOpt T w OPT →
        (∀ tape : Fin (budget C K n) → Bool,
          ∃ z : ℝ, (run P T w.d tape (budget C K n)).output = some z ∧
            (run P T w.d tape (budget C K n)).work ≤ budget C K n ∧
            (run P T w.d tape (budget C K n)).queries ≤ budget C K n) ∧
        (2 / 3 : ℝ) * 2 ^ (budget C K n) ≤
          ((Finset.univ.filter fun tape : Fin (budget C K n) → Bool =>
            ∃ z : ℝ, (run P T w.d tape (budget C K n)).output = some z ∧ OPT ≤ z ∧
              z ≤ (2 - η₀) * OPT).card : ℝ) := by sorry

end SublinearSteiner
