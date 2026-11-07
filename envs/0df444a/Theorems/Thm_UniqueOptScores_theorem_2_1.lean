-- Prove2me | Theorems.Thm_UniqueOptScores_theorem_2_1
-- name    : UniqueOptScores.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:53.80117+00:00
-- url     : https://prove2.me/theorems/60b5b7ad-2809-4430-8ed8-7df0b9ab43fc
-- title:
--   Theorem 2.1 — uniform polynomial obstruction, $N \le 24r^3(q+1)$
-- statement:
--   Throughout, $X, Y$ are disjoint sets of $N$ points, the oracle answers outside $X \cup Y$ are fixed, and a score system with candidates $C$ (finite, nonempty) evaluates each candidate by a deterministic query algorithm making at most $q$ membership queries and returning a score in $\{0,\dots,r\}$ on every support, with integers $r \ge 1$, $q \ge 0$. The system is correct on $P_r$: $U(S) = F(S)$ for every support $S$ with $|S\cap X|, |S\cap Y| \le r$, where $F(S) = [\,|S\cap X| = 1 \lor |S\cap Y| = 1\,]$ and $U(S)$ says that exactly one candidate attains the maximum score $v(S)$. A support is YES if it is in $P_r$ and satisfies $F$; $B + x$ denotes $B \cup \{x\}$.
--
--   If $U(S) = F(S)$ for every $S \in P_r$, then
--   $$
--   N \ \le\ 24\,r^3\,(q+1).
--   $$
--   The bound holds for adaptive and repeated queries, negative replies and arbitrary fixed exterior answers, and it does not depend on the number of candidates.
--
--   This finite obstruction is the key to separating $\mathrm{UO}^A_{\mathrm P}$ from disjunctive access: a polynomial-score evaluator has polynomially bounded $r$ and $q$ on input $1^n$, while the regions have $2^n$ points.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Theorem 2.1 (restated), p.22 (stated as Theorem 2.1, p.9)

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_maxScore
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_IsCorrect

namespace UniqueOptScores

/-- **Theorem 2.1 (uniform polynomial obstruction).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Theorem 2.1 (restated), p.22: "Let r ≥ 1 and q ≥ 0 be integers. If U(S) = F(S) for every
S ∈ P_r, then N ≤ 24r^3(q + 1). The conclusion allows adaptive queries, repeated queries, negative
replies, and arbitrary fixed exterior answers."

**Formalization Note.** The frame of §6 (p.22): `X, Y` disjoint finite sets of points with
`|X| = |Y| = N`, exterior answers `e`, a finite nonempty candidate type `ι` whose evaluations
`T c` are decision trees making at most `q` queries and returning scores at most `r` on every
support (`IsScoreSystem`), integers `r ≥ 1` and `q ≥ 0`, and correctness on `P_r` (`IsCorrect`).
`v(S)` is `maxScore T (supportOracle X Y e S)`; `B + x` is `insert x B`. There is no bound on the number of candidates. -/
theorem theorem_2_1 {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (X Y : Finset α) (N : ℕ) (hXY : Disjoint X Y) (hX : X.card = N) (hY : Y.card = N)
    (e : α → Bool) (T : ι → QTree α ℕ) (r q : ℕ) (hr : 1 ≤ r)
    (hT : IsScoreSystem X Y e T r q) (hcorr : IsCorrect X Y e T r) :
    N ≤ 24 * r ^ 3 * (q + 1) := by sorry

end UniqueOptScores
