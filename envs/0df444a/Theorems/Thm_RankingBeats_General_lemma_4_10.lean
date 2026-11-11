-- Prove2me | Theorems.Thm_RankingBeats_General_lemma_4_10
-- name    : RankingBeats.General.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:23.688349+00:00
-- url     : https://prove2.me/theorems/2d0c951b-4a95-4007-9da7-d7772c61ac39
-- title:
--   Lemma 4.10 — an inserted vertex is matched to its minimum-rank candidate match
-- statement:
--   $G=(V,E)$ is a finite simple graph. A rank vector $\vec x_{-w}$ (ranks in $[0,1)$) is fixed and $w$ is reinserted at rank $y\in[0,1)$, giving $\vec x_{-w}(y)$; all ranks of $\vec x_{-w}(y)$ are pairwise distinct. A neighbour $v$ of $w$ is a candidate match of $w$ at rank $y$ if $v$ is unmatched in $R(\vec x_{-w})$ or its match there has rank $>y$; $\mathrm{CM}_{\vec x_{-w}}(y)$ is the set of candidate matches. Then $w$ is matched in $R(\vec x_{-w}(y))$ to the smallest-ranked candidate match,
--   $$\text{match of } w \text{ in } R(\vec x_{-w}(y))=\arg\min_v\{x_v\mid v\in\mathrm{CM}_{\vec x_{-w}}(y)\},$$
--   and consequently $w$ is unmatched in $R(\vec x_{-w}(y))$ iff $\mathrm{CM}_{\vec x_{-w}}(y)=\emptyset$.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11), for the rank vector with the inserted rank → hypothesis Function.Injective (Function.update x w y): the inserted rank differs from all other ranks and those are pairwise distinct; reason: the paper's standing assumption for the vector x_{-w}(y), made an explicit binder
--   - encoding: a rank vector x_{-w} on V \ {w} → a full vector x : V → ℝ whose w-coordinate is ignored (ranking G {w} x and Function.update x w y do not read it); hx also asks x w ∈ [0, 1); reason: every x_{-w} extends to such an x, so the statement covers exactly the paper's vectors
--   - encoding: match of w in R(x_{-w}(y)) = arg min_v {x_v | v ∈ CM_{x_{-w}}(y)} → ∀ m, (w, m) ∈ R(x_{-w}(y)) ↔ (m ∈ CM ∧ ∀ v ∈ CM, x_m ≤ x_v); reason: the arg min is unique for distinct ranks, and the iff says w is matched exactly to it (and to nothing when CM = ∅)
--   - encoding: R(x_{-S}): Ranking with the vertices of S removed → ranking G S x, the run with S unavailable from the start and the other ranks unchanged; reason: the paper's own description of removal (p. 12)
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 15, Lemma 4.10

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Lemma 4.10** (Matching Description by Min-rank Candidate, p. 15). Reinserting `w` at rank
`y` into `x_{-w}`, `w` is matched in `R(x_{-w}(y))` exactly to the smallest-ranked candidate
match `arg min {x_v | v ∈ CM_{x_{-w}}(y)}`; hence `w` is unmatched iff `CM_{x_{-w}}(y) = ∅`. -/
theorem lemma_4_10 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (w : V)
    (x : V → ℝ) (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Set.Ico (0 : ℝ) 1)
    (hinj : Function.Injective (Function.update x w y)) :
    (∀ m, s(w, m) ∈ ranking G ∅ (Function.update x w y) ↔
      (m ∈ candidateMatches G x w y ∧ ∀ v ∈ candidateMatches G x w y, x m ≤ x v)) ∧
    (¬ IsMatched (ranking G ∅ (Function.update x w y)) w ↔ candidateMatches G x w y = ∅) := by sorry

end RankingBeats.General
