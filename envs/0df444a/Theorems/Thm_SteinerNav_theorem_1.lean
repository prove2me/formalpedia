-- Prove2me | Theorems.Thm_SteinerNav_theorem_1
-- name    : SteinerNav.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:29.339879+00:00
-- url     : https://prove2.me/theorems/4434ee6d-839c-4d8d-bbcd-5a869faa97e7
-- title:
--   Theorem 1 (corrected at $\Delta=1$) — a $(1+1/d)$-navigable graph with Steiner points, $O(n^{3/2}\sqrt{\log n(1+\log\Delta)})$ edges, short routes and $\frac{\alpha+1}{\alpha-1}$-approximate search
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $d\ge1$, let $P\subset\mathbb R^d$ be a set of $n\ge2$ points with aspect ratio $\Delta$, and let $\alpha=1+1/d$. There are a finite set $R$ of Steiner points and a directed graph $G=(P\cup R,E)$ such that:
--
--   1. $G$ is an $\alpha$-navigable graph with Steiner points for $P$;
--   2. $G$ is sparse:
--   $$|E|\ \le\ C\,n^{3/2}\sqrt{\ln n\,(1+\ln\Delta)} ;$$
--   3. $G$ has no self-loops and no Steiner-to-Steiner edges;
--   4. greedy search reaches every input point quickly: for every target $t\in P$, every run of greedy search toward $t$ has at most $\lfloor\log_\alpha\Delta\rfloor+2$ moves from a start in $P$ and at most $\lfloor\log_\alpha\Delta\rfloor+3$ moves from a start in $R$; every run that stops, stops at $t$; and from every start some run stops;
--   5. greedy search returns an approximate nearest neighbor for every query: for every $q\in\mathbb R^d$ and every start $x_0\in P\cup R$, some run stops at a local minimum, and at every local minimum $x$ reached by a run, the return rule of Lemma 6.5 (return $x$ if $x\in P$, else an out-neighbor of $x$ closest to $q$) returns something, and every value $y$ it can return lies in $P$ and satisfies
--   $$\|y-q\|\ \le\ \frac{\alpha+1}{\alpha-1}\,\|p-q\|\quad\text{for all } p\in P .$$
--
--   One graph serves every target, start and query. For $d=O(\log n)$ and $\Delta$ polynomial in $n$ this is a graph with $O(n^{3/2}\log n)$ edges on which greedy search takes $O(\log^2 n)$ steps and returns an $O(\log n)$-approximate nearest neighbor, while without Steiner points some such inputs need $\Omega(n^2)$ edges.
--
--   **Formalization Note** $C$ is chosen before $d$, $n$ and $P$; $R$ and $E$ before the target, start and query. Runs range over all resolutions of ties. Logarithms are natural; another fixed base changes only $C$. The step bound applies to input-point targets only, as in the paper's sentence; for arbitrary queries the guarantee is at termination (the paper notes on p.25 that reaching a local minimum can take linearly many moves).
--
--   Differences from the source:
--   - correction: "within O(⌈log_α Δ⌉) steps" → at most ⌊log_α Δ⌋ + 2 moves from an input start and ⌊log_α Δ⌋ + 3 from a Steiner start (Lemma 6.7's explicit bound); reason: at Δ = 1 the printed bound is O(0) = 0, false for P = {0, e₁} ⊂ ℝ^d (n = 2, Δ = 1), where a search from 0 to e₁ must move once; for Δ > 1, ⌊log_α Δ⌋ + 3 ≤ 4⌈log_α Δ⌉, so the printed bound follows.
--   - generalization: the graph's properties in Theorem 1 → also no self-loops and no Steiner-to-Steiner edges; reason: Theorem 3's graph has both and the paper's proof of the search guarantees (Lemmas 6.5, 6.7) uses the second; dropping the clause gives the page's statement.
--   - reading: "greedy search reaches any input point" (start unspecified, ties unspecified) → every start in P ∪ R and every tie-breaking, with existence of a stopping run; reason: the strongest reading, and the one Lemmas 6.5 and 6.7 prove.
--   - reading: "a set of n points in ℝ^d" → n ≥ 2 and d ≥ 1; reason: the paper's standing assumption (§3, p.5, "Throughout, P ⊂ ℝ^d is a set of n ≥ 2 distinct points, d ≥ 1"); the aspect ratio is undefined for n ≤ 1.
--   - encoding: O(n^{3/2}√(log n(1 + log Δ))) → an absolute constant C before d, n and P, natural logarithms; reason: the meaning of O(·) here, and a change of log base changes only C.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 1, p.3; proof via Theorem 3 (p.8), Lemma 6.5 (p.22), Lemma 6.7 (p.23)

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_GreedyRun

namespace SteinerNav

/-- Theorem 1 (step bound corrected at `Δ = 1`): there is an absolute constant `C` such that for every
`d ≥ 1` and every `P ⊂ ℝ^d` with `n = |P| ≥ 2` and aspect ratio `Δ`, for `α = 1 + 1/d` there are a finite `R`
and a graph `E` on `P ∪ R` such that: (1) `E` is `α`-navigable with Steiner points `R`; (2) `|E| ≤ C n^{3/2}
√(ln n (1 + ln Δ))`; (3) `E` has no self-loops and no Steiner-to-Steiner edges; (4) for every target
`t ∈ P`, greedy search reaches `t` from every start of `P ∪ R` within `⌊log_α Δ⌋ + 3` moves
(`⌊log_α Δ⌋ + 2` from an input point); (5) for every query `q` and start `x₀ ∈ P ∪ R`, greedy search
stops, and at every local minimum it stops at, the return rule gives an input point that is an
`(α+1)/(α−1)`-approximate nearest neighbor (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Theorem 1, p.3; proof: Theorem 3, Lemma 6.5, Lemma 6.7).

**Formalization Note** `C` comes before `d`, `n` and `P`; `R` and `E` come before `t`, `x₀` and `q`, so one
graph serves every search. Runs range over all resolutions of ties. Logarithms are natural. The printed
step bound `O(⌈log_α Δ⌉)` is `0` at `Δ = 1`, false for `P = {0, e₁}`, so the paper's explicit bound of
Lemma 6.7 is stated; for `Δ > 1` it implies the printed one. Clause (5) has no step bound. -/
theorem theorem_1 : ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ P : Finset (Pt d), 2 ≤ P.card →
    let n : ℝ := (P.card : ℝ)
    let α : ℝ := 1 + 1 / (d : ℝ)
    let Δ : ℝ := aspectRatio P
    ∃ (R : Finset (Pt d)) (E : Finset (Pt d × Pt d)),
      IsSteinerNavigable α P R E ∧
      (E.card : ℝ) ≤ C * n ^ (3 / 2 : ℝ) * Real.sqrt (Real.log n * (1 + Real.log Δ)) ∧
      (∀ x, (x, x) ∉ E) ∧
      NoSteinerToSteiner R P E ∧
      (∀ t ∈ P,
        (∀ x₀ ∈ P, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α Δ⌋₊ + 2) ∧
        (∀ x₀ ∈ R, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α Δ⌋₊ + 3) ∧
        (∀ x₀ ∈ P ∪ R, ∀ k x, GreedyRun E t x₀ k x → GreedyLocalMin E t x → x = t) ∧
        (∀ x₀ ∈ P ∪ R, ∃ k x, GreedyRun E t x₀ k x ∧ GreedyLocalMin E t x)) ∧
      (∀ q : Pt d, ∀ x₀ ∈ P ∪ R,
        (∃ k x, GreedyRun E q x₀ k x ∧ GreedyLocalMin E q x) ∧
        ∀ k x, GreedyRun E q x₀ k x → GreedyLocalMin E q x →
          (∃ y, GreedyReturns E P q x y) ∧
          ∀ y, GreedyReturns E P q x y →
            y ∈ P ∧ ∀ p ∈ P, dist y q ≤ (α + 1) / (α - 1) * dist p q) := by sorry

end SteinerNav
