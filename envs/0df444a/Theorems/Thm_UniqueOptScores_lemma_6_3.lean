-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_6_3
-- name    : UniqueOptScores.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:50.444161+00:00
-- url     : https://prove2.me/theorems/1d69facc-9dbf-41e5-9909-553173ab6907
-- title:
--   Lemma 6.3 — one selection step, $|D'| \ge \alpha d - A_0$
-- statement:
--   Throughout, $X, Y$ are disjoint sets of $N$ points, the oracle answers outside $X \cup Y$ are fixed, and a score system with candidates $C$ (finite, nonempty) evaluates each candidate by a deterministic query algorithm making at most $q$ membership queries and returning a score in $\{0,\dots,r\}$ on every support, with integers $r \ge 1$, $q \ge 0$. The system is correct on $P_r$: $U(S) = F(S)$ for every support $S$ with $|S\cap X|, |S\cap Y| \le r$, where $F(S) = [\,|S\cap X| = 1 \lor |S\cap Y| = 1\,]$ and $U(S)$ says that exactly one candidate attains the maximum score $v(S)$. A support is YES if it is in $P_r$ and satisfies $F$; $B + x$ denotes $B \cup \{x\}$.
--
--   Set (eq. (3))
--   $$
--   H = 2r(q+1), \qquad A_0 = (2r^2+1)(q+1) = rH + q + 1, \qquad \alpha = 1 - \frac{1}{2r}.
--   $$
--   Let $B$ be YES and let $D$ be a set of $d$ points outside $B$ such that every $B + u$ and every $B + x + u$ ($x, u \in D$ distinct) is YES and $v(B + u) > v(B)$ for every $u \in D$. If $d > rH$, there are $x \in D$ and $D' \subseteq D \setminus \{x\}$ with
--   $$
--   v(B + x + u) > v(B + x) \quad (u \in D'), \qquad |D'| \ \ge\ \alpha d - A_0 .
--   $$
--
--   Selecting the lowest sufficiently large score class keeps a fraction $\alpha$ of the extensions at each step, which is where the polynomial dependence on $r$ in Theorem 2.1 comes from.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
--   - encoding: H, A0, α of eq. (3) and the bound αd − A0 → the constants written out: r·(2r(q+1)) < |D| and (1 − 1/(2r))·|D| − (2r²+1)(q+1) ≤ |D′| in ℝ; reason: same numbers; real arithmetic avoids truncation
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 6.3, p.23, with eq. (3), p.23

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_maxScore
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_IsCorrect
import Definitions.Def_UniqueOptScores_IsYes

namespace UniqueOptScores

/-- **Lemma 6.3 (one selection step).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 6.3, p.23, with the constants of eq. (3), p.23 (`H = 2r(q + 1)`,
`A0 = (2r² + 1)(q + 1)`, `α = 1 − 1/(2r)`): "Let B be YES and let D be a set of d points outside B.
Suppose all B + u and all B + x + u for distinct x, u ∈ D are YES, and v(B + u) > v(B) for every
u ∈ D. If d > rH, there are x ∈ D and D′ ⊆ D \ {x} such that v(B + x + u) > v(B + x) (u ∈ D′),
|D′| ≥ αd − A0."

**Formalization Note.** The frame of §6 (p.22): `X, Y` disjoint finite sets of points with
`|X| = |Y| = N`, exterior answers `e`, a finite nonempty candidate type `ι` whose evaluations
`T c` are decision trees making at most `q` queries and returning scores at most `r` on every
support (`IsScoreSystem`), integers `r ≥ 1` and `q ≥ 0`, and correctness on `P_r` (`IsCorrect`).
`v(S)` is `maxScore T (supportOracle X Y e S)`; `B + x` is `insert x B`. `B + x + u` is `insert u (insert x B)`; `αd − A₀` is computed in `ℝ`. -/
theorem lemma_6_3 {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (X Y : Finset α) (N : ℕ) (hXY : Disjoint X Y) (hX : X.card = N) (hY : Y.card = N)
    (e : α → Bool) (T : ι → QTree α ℕ) (r q : ℕ) (hr : 1 ≤ r)
    (hT : IsScoreSystem X Y e T r q) (hcorr : IsCorrect X Y e T r)
    (B D : Finset α) (hB : IsYes r X Y B) (hDB : Disjoint D B)
    (hDu : ∀ u ∈ D, IsYes r X Y (insert u B))
    (hDxu : ∀ x ∈ D, ∀ u ∈ D, x ≠ u → IsYes r X Y (insert u (insert x B)))
    (hrise : ∀ u ∈ D, maxScore T (supportOracle X Y e B) <
      maxScore T (supportOracle X Y e (insert u B)))
    (hd : r * (2 * r * (q + 1)) < D.card) :
    ∃ x ∈ D, ∃ D' ⊆ D.erase x,
      (∀ u ∈ D', maxScore T (supportOracle X Y e (insert x B)) <
        maxScore T (supportOracle X Y e (insert u (insert x B)))) ∧
      (1 - 1 / (2 * (r : ℝ))) * D.card - (2 * (r : ℝ) ^ 2 + 1) * ((q : ℝ) + 1) ≤ D'.card := by sorry

end UniqueOptScores
