-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_6_1
-- name    : UniqueOptScores.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:43.434481+00:00
-- url     : https://prove2.me/theorems/a48b3931-4942-43f9-b9f8-eb2ffd676037
-- title:
--   Lemma 6.1 — collision forces a rise
-- statement:
--   Throughout, $X, Y$ are disjoint sets of $N$ points, the oracle answers outside $X \cup Y$ are fixed, and a score system with candidates $C$ (finite, nonempty) evaluates each candidate by a deterministic query algorithm making at most $q$ membership queries and returning a score in $\{0,\dots,r\}$ on every support, with integers $r \ge 1$, $q \ge 0$. The system is correct on $P_r$: $U(S) = F(S)$ for every support $S$ with $|S\cap X|, |S\cap Y| \le r$, where $F(S) = [\,|S\cap X| = 1 \lor |S\cap Y| = 1\,]$ and $U(S)$ says that exactly one candidate attains the maximum score $v(S)$. A support is YES if it is in $P_r$ and satisfies $F$; $B + x$ denotes $B \cup \{x\}$.
--
--   Let $B$ be a support and $x, u \notin B$ distinct points such that $B + x$, $B + u$ and $B + x + u$ are YES supports and
--   $$
--   v(B + x) = v(B + u) = t > v(B).
--   $$
--   If the maximizing candidate on $B + x$ does not query $u$, and the maximizing candidate on $B + u$ does not query $x$, then
--   $$
--   v(B + x + u) > t .
--   $$
--
--   This collision step is the basic way the uniform obstruction forces the maximum score to rise.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
--   - encoding: "the maximizing transcript on B + x avoids u" → every candidate attaining v(B + x) does not query u (and symmetrically); reason: on a YES support correctness makes the maximizing candidate unique, so the two statements coincide
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 6.1, p.22 (frame and standing assumptions of Section 6, p.22)

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_maxScore
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_IsCorrect
import Definitions.Def_UniqueOptScores_IsYes

namespace UniqueOptScores

/-- **Lemma 6.1 (collision forces a rise).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 6.1, p.22: "Let x, u ∉ B be distinct. Suppose B + x, B + u, and B + x + u are YES
supports, and v(B + x) = v(B + u) = t > v(B). If the maximizing transcript on B + x avoids u, and that
on B + u avoids x, then v(B + x + u) > t."

**Formalization Note.** The frame of §6 (p.22): `X, Y` disjoint finite sets of points with
`|X| = |Y| = N`, exterior answers `e`, a finite nonempty candidate type `ι` whose evaluations
`T c` are decision trees making at most `q` queries and returning scores at most `r` on every
support (`IsScoreSystem`), integers `r ≥ 1` and `q ≥ 0`, and correctness on `P_r` (`IsCorrect`).
`v(S)` is `maxScore T (supportOracle X Y e S)`; `B + x` is `insert x B`. "The maximizing transcript on `B + x` avoids `u`" is stated for every candidate attaining
the maximum on `B + x` (by correctness there is exactly one). -/
theorem lemma_6_1 {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (X Y : Finset α) (N : ℕ) (hXY : Disjoint X Y) (hX : X.card = N) (hY : Y.card = N)
    (e : α → Bool) (T : ι → QTree α ℕ) (r q : ℕ) (hr : 1 ≤ r)
    (hT : IsScoreSystem X Y e T r q) (hcorr : IsCorrect X Y e T r)
    (B : Finset α) (x u : α) (hxB : x ∉ B) (huB : u ∉ B) (hxu : x ≠ u)
    (hYx : IsYes r X Y (insert x B)) (hYu : IsYes r X Y (insert u B))
    (hYxu : IsYes r X Y (insert u (insert x B))) (t : ℕ)
    (hvx : maxScore T (supportOracle X Y e (insert x B)) = t)
    (hvu : maxScore T (supportOracle X Y e (insert u B)) = t)
    (hvB : maxScore T (supportOracle X Y e B) < t)
    (havoid_x : ∀ c : ι, (T c).eval (supportOracle X Y e (insert x B)) = t →
      u ∉ (T c).queries (supportOracle X Y e (insert x B)))
    (havoid_u : ∀ c : ι, (T c).eval (supportOracle X Y e (insert u B)) = t →
      x ∉ (T c).queries (supportOracle X Y e (insert u B))) :
    t < maxScore T (supportOracle X Y e (insert u (insert x B))) := by sorry

end UniqueOptScores
