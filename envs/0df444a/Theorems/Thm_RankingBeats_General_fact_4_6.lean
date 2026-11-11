-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_6
-- name    : RankingBeats.General.fact_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:38.299333+00:00
-- url     : https://prove2.me/theorems/351249e7-8896-41ed-ad11-d3fa0862c4e0
-- title:
--   Fact 4.6 — on an even alternating path every even-indexed vertex blocks the endpoint
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix a vertex $v$ and suppose $\mathrm{AltPath}(\vec x,\vec x_{-v})=(u_0,\dots,u_k)$, $u_0=v$, has even length $k\ge2$. Then $u_k$ is unmatched in $R(\vec x)$, and $u_i$ is a blocker of $u_k$ for every even $i<k$:
--   $$u_k\notin V(R(\vec x)),\qquad u_k\in V(R(\vec x_{-u_i}))\quad(i<k\text{ even}).$$
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - encoding: AltPath(x, x_{-v}) = (u_0, ..., u_k) → hypothesis IsPathFrom (altPath G x v) v p, with u_i = p.getD i v and k = p.length - 1; reason: the path with u_0 = v of Lemma 4.1
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 14, Fact 4.6

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_QueryCommit
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.6** (Blockers in Alternating Path: Even, p. 14). If `AltPath(x, x_{-v}) =
(u_0, …, u_k)` has even length `k ≥ 2`, then `u_k` is unmatched in `R(x)` and `u_i` is a blocker
of `u_k` for every even `i < k`. -/
theorem fact_4_6 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (v : V) (p : List V)
    (hp : IsPathFrom (altPath G x v) v p) (hk : Even (p.length - 1)) (hk2 : 2 ≤ p.length - 1) :
    ¬ IsMatched (ranking G ∅ x) (p.getD (p.length - 1) v) ∧
      ∀ i, Even i → i < p.length - 1 → IsVictim G x (p.getD (p.length - 1) v) (p.getD i v) := by sorry

end RankingBeats.General
