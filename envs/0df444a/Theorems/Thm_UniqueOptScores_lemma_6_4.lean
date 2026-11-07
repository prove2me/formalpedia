-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_6_4
-- name    : UniqueOptScores.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:30:25.286202+00:00
-- url     : https://prove2.me/theorems/ac9657fe-b365-445b-8395-6381bb7c6c50
-- title:
--   Lemma 6.4 — no initial fan with $d_0 > 2r(A_0 + H)$
-- statement:
--   Throughout, $X, Y$ are disjoint sets of $N$ points, the oracle answers outside $X \cup Y$ are fixed, and a score system with candidates $C$ (finite, nonempty) evaluates each candidate by a deterministic query algorithm making at most $q$ membership queries and returning a score in $\{0,\dots,r\}$ on every support, with integers $r \ge 1$, $q \ge 0$. The system is correct on $P_r$: $U(S) = F(S)$ for every support $S$ with $|S\cap X|, |S\cap Y| \le r$, where $F(S) = [\,|S\cap X| = 1 \lor |S\cap Y| = 1\,]$ and $U(S)$ says that exactly one candidate attains the maximum score $v(S)$. A support is YES if it is in $P_r$ and satisfies $F$; $B + x$ denotes $B \cup \{x\}$.
--
--   A **fan** is a pair $(B, D)$ where $B$ contains one point of $Y$, $D \subseteq X \setminus B$, and every extension $B + u$ ($u \in D$) has maximum strictly larger than $v(B)$. With $H = 2r(q+1)$ and $A_0 = (2r^2+1)(q+1)$, a correct score system has no fan with $B_0 = \{y\}$ and
--   $$
--   d_0 = |D_0| > 2r(A_0 + H).
--   $$
--   Equivalently: for every $y \in Y$ and every $D_0 \subseteq X$ with $v(\{y\} + u) > v(\{y\})$ for all $u \in D_0$, one has $|D_0| \le 2r(A_0 + H)$.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
--   - encoding: "a fan with B0 = {y} and d0 > 2r(A0 + H) cannot exist" → for every y ∈ Y and D₀ ⊆ X whose one-point extensions raise the maximum, |D₀| ≤ 2r((2r²+1)(q+1) + 2r(q+1)); reason: contrapositive form; D₀ ⊆ X is D₀ ⊆ X ∖ {y} because X ∩ Y = ∅, and the supports {y} + u lie in P_r for r ≥ 1, so the fan's occupancy proviso holds automatically
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 6.4, p.24, with the definition of a fan, p.24, and eq. (3), p.23

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_maxScore
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_IsCorrect

namespace UniqueOptScores

/-- **Lemma 6.4 (no large initial fan).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 6.4, p.24, with the fan definition of p.24 ("Call (B, D) a fan if B contains one point
of Y , D ⊆ X \ B, and every extension B + u, u ∈ D, has maximum strictly larger than v(B)") and the
constants of eq. (3), p.23: "A fan with B0 = {y} and d0 = |D0| > 2r(A0 + H) cannot exist in a
correct score system."

**Formalization Note.** The frame of §6 (p.22): `X, Y` disjoint finite sets of points with
`|X| = |Y| = N`, exterior answers `e`, a finite nonempty candidate type `ι` whose evaluations
`T c` are decision trees making at most `q` queries and returning scores at most `r` on every
support (`IsScoreSystem`), integers `r ≥ 1` and `q ≥ 0`, and correctness on `P_r` (`IsCorrect`).
`v(S)` is `maxScore T (supportOracle X Y e S)`; `B + x` is `insert x B`. The fan is `B₀ = {y}` with `y ∈ Y` and `D₀ ⊆ X` (which is `X ∖ B₀`, as `X ∩ Y = ∅`);
"cannot exist" is `|D₀| ≤ 2r(A₀ + H)` with `A₀ + H = (2r² + 1)(q + 1) + 2r(q + 1)`. -/
theorem lemma_6_4 {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (X Y : Finset α) (N : ℕ) (hXY : Disjoint X Y) (hX : X.card = N) (hY : Y.card = N)
    (e : α → Bool) (T : ι → QTree α ℕ) (r q : ℕ) (hr : 1 ≤ r)
    (hT : IsScoreSystem X Y e T r q) (hcorr : IsCorrect X Y e T r)
    (y : α) (hy : y ∈ Y) (D₀ : Finset α) (hD₀ : D₀ ⊆ X)
    (hfan : ∀ u ∈ D₀, maxScore T (supportOracle X Y e {y}) <
      maxScore T (supportOracle X Y e (insert u {y}))) :
    D₀.card ≤ 2 * r * ((2 * r ^ 2 + 1) * (q + 1) + 2 * r * (q + 1)) := by sorry

end UniqueOptScores
