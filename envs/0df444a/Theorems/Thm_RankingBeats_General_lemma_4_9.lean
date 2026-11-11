-- Prove2me | Theorems.Thm_RankingBeats_General_lemma_4_9
-- name    : RankingBeats.General.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:12.668237+00:00
-- url     : https://prove2.me/theorems/3e51b05b-3d46-4c6a-8e90-9cd416b9b643
-- title:
--   Lemma 4.9 — three matching guarantees when w is reinserted at rank y
-- statement:
--   $G=(V,E)$ is a finite simple graph. A rank vector $\vec x_{-w}$ (ranks in $[0,1)$) is fixed and $w$ is reinserted at rank $y\in[0,1)$, giving $\vec x_{-w}(y)$; all ranks of $\vec x_{-w}(y)$ are pairwise distinct. Let $(u,w)\in E$ and let $v$ be the match of $u$ in $R(\vec x_{-w})$, if it exists.
--   1. If $u$ is unmatched in $R(\vec x_{-w})$, or $y<x_v$, then $w$ is matched in $R(\vec x_{-w}(y))$ and its match has rank $\le x_u$.
--   2. If $y>x_u$, then $u$ is not worse off in $R(\vec x_{-w}(y))$ than in $R(\vec x_{-w})$.
--   3. If $u$ is worse off in $R(\vec x_{-w}(y))$ than in $R(\vec x_{-w})$, then $w$ is matched in $R(\vec x_{-w}(y))$ and its match has rank $\le x_v$.
--
--   $$\big(u\notin V(R(\vec x_{-w}))\ \lor\ y<x_v\big)\ \Longrightarrow\ w\in V(R(\vec x_{-w}(y)))\ \text{and}\ x_{\mathrm{match}(w)}\le x_u.$$
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11), for the rank vector with the inserted rank → hypothesis Function.Injective (Function.update x w y): the inserted rank differs from all other ranks and those are pairwise distinct; reason: the paper's standing assumption for the vector x_{-w}(y), made an explicit binder
--   - encoding: a rank vector x_{-w} on V \ {w} → a full vector x : V → ℝ whose w-coordinate is ignored (ranking G {w} x and Function.update x w y do not read it); hx also asks x w ∈ [0, 1); reason: every x_{-w} extends to such an x, so the statement covers exactly the paper's vectors
--   - encoding: R(x_{-S}): Ranking with the vertices of S removed → ranking G S x, the run with S unavailable from the start and the other ranks unchanged; reason: the paper's own description of removal (p. 12)
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 15, Lemma 4.9

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Lemma 4.9** (Basic Matching Properties: Inserting, p. 15). Let `(u, w) ∈ E`, fix `x_{-w}`
(the coordinates of `x` off `w`) and reinsert `w` at rank `y`
(`x_{-w}(y) = Function.update x w y`). (1) If `u` is unmatched in `R(x_{-w})` or its match `v`
there has `y < x_v`, then `w` is matched in `R(x_{-w}(y))` to a vertex of rank `≤ x_u`.
(2) If `y > x_u`, then `u` is not worse off in `R(x_{-w}(y))`. (3) If `u` is made worse off,
then `w` is matched in `R(x_{-w}(y))` to a vertex of rank `≤ x_v`. -/
theorem lemma_4_9 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (u w : V)
    (huw : G.Adj u w) (x : V → ℝ) (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (y : ℝ)
    (hy : y ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective (Function.update x w y)) :
    ((¬ IsMatched (ranking G {w} x) u ∨ ∃ v, s(u, v) ∈ ranking G {w} x ∧ y < x v) →
      IsMatched (ranking G ∅ (Function.update x w y)) w ∧
        ∀ m, s(w, m) ∈ ranking G ∅ (Function.update x w y) → Function.update x w y m ≤ x u) ∧
    (x u < y →
      ¬ BetterOff (ranking G {w} x) x (ranking G ∅ (Function.update x w y))
          (Function.update x w y) u) ∧
    (BetterOff (ranking G {w} x) x (ranking G ∅ (Function.update x w y))
        (Function.update x w y) u →
      IsMatched (ranking G ∅ (Function.update x w y)) w ∧
        ∀ v m, s(u, v) ∈ ranking G {w} x → s(w, m) ∈ ranking G ∅ (Function.update x w y) →
          Function.update x w y m ≤ x v) := by sorry

end RankingBeats.General
