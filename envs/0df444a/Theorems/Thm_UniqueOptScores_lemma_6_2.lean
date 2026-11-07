-- Prove2me | Theorems.Thm_UniqueOptScores_lemma_6_2
-- name    : UniqueOptScores.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:54.189093+00:00
-- url     : https://prove2.me/theorems/7c8bed70-99ee-4e0e-bd57-b6022d7106dc
-- title:
--   Lemma 6.2 — the initial fan, $|D_0| \ge N/2 - 2q$
-- statement:
--   Throughout, $X, Y$ are disjoint sets of $N$ points, the oracle answers outside $X \cup Y$ are fixed, and a score system with candidates $C$ (finite, nonempty) evaluates each candidate by a deterministic query algorithm making at most $q$ membership queries and returning a score in $\{0,\dots,r\}$ on every support, with integers $r \ge 1$, $q \ge 0$. The system is correct on $P_r$: $U(S) = F(S)$ for every support $S$ with $|S\cap X|, |S\cap Y| \le r$, where $F(S) = [\,|S\cap X| = 1 \lor |S\cap Y| = 1\,]$ and $U(S)$ says that exactly one candidate attains the maximum score $v(S)$. A support is YES if it is in $P_r$ and satisfies $F$; $B + x$ denotes $B \cup \{x\}$.
--
--   If $N > 4q$ then, possibly after exchanging $X$ and $Y$, there are a point $y \in Y$ and a set $D_0 \subseteq X$ with
--   $$
--   v(\{y, x\}) > v(\{y\}) \quad (x \in D_0), \qquad |D_0| \ \ge\ \frac N2 - 2q .
--   $$
--
--   The set $D_0$ is the initial family of score-raising extensions from which the iteration of Lemmas 6.3 and 6.4 starts.
--
--   Differences from the source:
--   - encoding: total deterministic oracle algorithm with scores in {0,…,r} and at most q membership queries (for every support S) → decision trees QTree α ℕ with at most q queried points and score ≤ r under the oracle of every support S ⊆ X ∪ Y (IsScoreSystem); finite nonempty candidate type ι; reason: a total deterministic query algorithm is a decision tree; the bounds are per support as on p.8; same instances
--   - encoding: "possibly exchanging X and Y" → the disjunction of the statement for (X, Y) and for (Y, X); reason: literal meaning
--   - encoding: |D0| ≥ N/2 − 2q → (N : ℝ)/2 − 2q ≤ |D₀| in ℝ; reason: avoids truncated natural subtraction and division; same inequality
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 6.2, p.23

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_supportOracle
import Definitions.Def_UniqueOptScores_maxScore
import Definitions.Def_UniqueOptScores_IsScoreSystem
import Definitions.Def_UniqueOptScores_IsCorrect

namespace UniqueOptScores

/-- **Lemma 6.2 (the initial fan).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 6.2, p.23: "If N > 4q, then, possibly exchanging X and Y , there are y ∈ Y and
D0 ⊆ X with v({y, x}) > v({y}) (x ∈ D0), |D0| ≥ N/2 − 2q."

**Formalization Note.** The frame of §6 (p.22): `X, Y` disjoint finite sets of points with
`|X| = |Y| = N`, exterior answers `e`, a finite nonempty candidate type `ι` whose evaluations
`T c` are decision trees making at most `q` queries and returning scores at most `r` on every
support (`IsScoreSystem`), integers `r ≥ 1` and `q ≥ 0`, and correctness on `P_r` (`IsCorrect`).
`v(S)` is `maxScore T (supportOracle X Y e S)`; `B + x` is `insert x B`. "Possibly exchanging `X` and `Y`" is the disjunction of the two orientations; the bound
`N/2 − 2q` is computed in `ℝ`. -/
theorem lemma_6_2 {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (X Y : Finset α) (N : ℕ) (hXY : Disjoint X Y) (hX : X.card = N) (hY : Y.card = N)
    (e : α → Bool) (T : ι → QTree α ℕ) (r q : ℕ) (hr : 1 ≤ r)
    (hT : IsScoreSystem X Y e T r q) (hcorr : IsCorrect X Y e T r) (hN : 4 * q < N) :
    (∃ y ∈ Y, ∃ D₀ ⊆ X, (∀ x ∈ D₀, maxScore T (supportOracle X Y e {y}) <
        maxScore T (supportOracle X Y e {y, x})) ∧ (N : ℝ) / 2 - 2 * q ≤ D₀.card) ∨
    (∃ y ∈ X, ∃ D₀ ⊆ Y, (∀ x ∈ D₀, maxScore T (supportOracle X Y e {y}) <
        maxScore T (supportOracle X Y e {y, x})) ∧ (N : ℝ) / 2 - 2 * q ≤ D₀.card) := by sorry

end UniqueOptScores
