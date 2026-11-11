-- Prove2me | Theorems.Thm_RankingBeats_General_lemma_4_11
-- name    : RankingBeats.General.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:14.7801+00:00
-- url     : https://prove2.me/theorems/42cd7d8e-fcfb-4b52-a89f-590e5d62dbef
-- title:
--   Lemma 4.11 — removing an unmatched vertex or a matched pair leaves the matching; rank bounds when only w is removed
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix a vertex $w$.
--   - If $w$ is not matched in $R(\vec x)$, then $R(\vec x)=R(\vec x_{-w})$.
--   - If $w$ is matched to $v$ in $R(\vec x)$, then $R(\vec x)=R(\vec x_{-vw})\cup\{(v,w)\}$.
--   - If only $w$ is removed (and $w$ is matched to $v$ in $R(\vec x)$):
--     1. if a vertex $u\neq w$ is better off in $R(\vec x_{-w})$ than in $R(\vec x)$, then $x_u>x_w$, and its match in $R(\vec x_{-w})$ has rank $\ge x_v$;
--     2. if a vertex $u\neq w$ is worse off in $R(\vec x_{-w})$ than in $R(\vec x)$, then $x_u\ge x_v$, and its match in $R(\vec x_{-w})$, if any, has rank $>x_w$.
--
--   $$R(\vec x)=R(\vec x_{-vw})\cup\{(v,w)\}\quad\text{whenever }(v,w)\in R(\vec x).$$
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - encoding: R(x_{-S}): Ranking with the vertices of S removed → ranking G S x, the run with S unavailable from the start and the other ranks unchanged; reason: the paper's own description of removal (p. 12)
--   - reading: 'If only w is removed, then ... rank ≥ x_v ... x_u ≥ x_v', with v the match of w → the clauses mentioning v are stated for every v with (w, v) ∈ R(x); the clauses x_u > x_w and 'rank > x_w' are stated without that hypothesis; reason: v is introduced as the match of w; when w is unmatched the first sentence gives R(x) = R(x_{-w}), so nobody is better or worse off and the clauses without v hold vacuously
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 16, Lemma 4.11

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Lemma 4.11** (Basic Matching Properties: Removing, p. 16). If `w` is unmatched in `R(x)`,
then `R(x) = R(x_{-w})`. If `w` is matched to `v`, then `R(x) = R(x_{-vw}) ∪ {(v, w)}`. If only
`w` is removed: (1) a vertex `u ≠ w` that becomes better off in `R(x_{-w})` has `x_u > x_w`, and
its better match has rank `≥ x_v`; (2) a vertex `u ≠ w` that becomes worse off in `R(x_{-w})` has
`x_u ≥ x_v`, and its worse match (if any) has rank `> x_w`. -/
theorem lemma_4_11 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (w : V) :
    (¬ IsMatched (ranking G ∅ x) w → ranking G ∅ x = ranking G {w} x) ∧
    (∀ v, s(w, v) ∈ ranking G ∅ x → ranking G ∅ x = insert s(v, w) (ranking G {v, w} x)) ∧
    (∀ u, u ≠ w → BetterOff (ranking G {w} x) x (ranking G ∅ x) x u →
      x w < x u ∧
        ∀ v m, s(w, v) ∈ ranking G ∅ x → s(u, m) ∈ ranking G {w} x → x v ≤ x m) ∧
    (∀ u, u ≠ w → BetterOff (ranking G ∅ x) x (ranking G {w} x) x u →
      (∀ v, s(w, v) ∈ ranking G ∅ x → x v ≤ x u) ∧
        ∀ m, s(u, m) ∈ ranking G {w} x → x w < x m) := by sorry

end RankingBeats.General
