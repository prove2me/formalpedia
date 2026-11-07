-- Prove2me | Theorems.Thm_SteinerNav_lemma_6_7
-- name    : SteinerNav.lemma_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:35.621563+00:00
-- url     : https://prove2.me/theorems/8b2562a2-f52b-4d85-a913-4fd72967178e
-- title:
--   Lemma 6.7 — greedy routing to an input point takes at most $\lfloor\log_\alpha\Delta\rfloor+2$ moves (one more from a Steiner start)
-- statement:
--   Let $\alpha>1$, let $P$ have $n\ge2$ points with aspect ratio $\Delta$, and let $G=(P\cup R,E)$ be an $\alpha$-navigable graph with Steiner points for $P$ with no Steiner-to-Steiner edges. Fix a target $t\in P$. Then for greedy routing toward $t$:
--
--   1. from every input start $x_0\in P$, every run has at most $\lfloor\log_\alpha\Delta\rfloor+2$ moves;
--   2. from every Steiner start $x_0\in R$, every run has at most $\lfloor\log_\alpha\Delta\rfloor+3$ moves;
--   3. from every start in $P\cup R$, every run that stops at a local minimum stops at $t$;
--   4. from every start in $P\cup R$, some run stops at a local minimum.
--
--   Here $\Delta$ is the aspect ratio of $P$ alone; nothing is assumed about the distances of the Steiner points.
--
--   **Formalization Note** "Reaches $t$ in at most $k$ moves" is clauses 1–4 together: every tie-breaking is covered, the search cannot stop elsewhere, and it does stop.
--
--   Differences from the source: none.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 6.7, p.23; σ, D, Δ of P, p.23

import Mathlib
import Definitions.Def_SteinerNav_IsSteinerNavigable
import Definitions.Def_SteinerNav_aspectRatio
import Definitions.Def_SteinerNav_GreedyRun

namespace SteinerNav

/-- Lemma 6.7: if `G` is Steiner `α`-navigable with no Steiner-to-Steiner edges, greedy routing to `t ∈ P`
reaches `t` in at most `⌊log_α Δ⌋ + 2` moves from an input point and `⌊log_α Δ⌋ + 3` from a Steiner vertex
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 6.7, p.23).

**Formalization Note** "Reaches" is three clauses: every run respects the bound, every run that stops
at a local minimum stops at `t`, and a run that stops exists. All resolutions of ties are covered. -/
theorem lemma_6_7 {d : ℕ} (α : ℝ) (hα : 1 < α) (P R : Finset (Pt d)) (E : Finset (Pt d × Pt d))
    (hn : 2 ≤ P.card) (hG : IsSteinerNavigable α P R E) (hN : NoSteinerToSteiner R P E)
    (t : Pt d) (ht : t ∈ P) :
    (∀ x₀ ∈ P, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α (aspectRatio P)⌋₊ + 2) ∧
      (∀ x₀ ∈ R, ∀ k x, GreedyRun E t x₀ k x → k ≤ ⌊Real.logb α (aspectRatio P)⌋₊ + 3) ∧
      (∀ x₀ ∈ P ∪ R, ∀ k x, GreedyRun E t x₀ k x → GreedyLocalMin E t x → x = t) ∧
      (∀ x₀ ∈ P ∪ R, ∃ k x, GreedyRun E t x₀ k x ∧ GreedyLocalMin E t x) := by sorry

end SteinerNav
