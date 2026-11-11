-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_5
-- name    : RankingBeats.General.fact_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:29.6902+00:00
-- url     : https://prove2.me/theorems/62dc3265-7b9a-42c7-98b0-e97745ac4795
-- title:
--   Fact 4.5 — v has a victim w iff the alternating path has even length k ≥ 2 ending at w; victims are unique
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix a vertex $v$. For every vertex $w$, $w$ is a victim of $v$ (unmatched in $R(\vec x)$, matched in $R(\vec x_{-v})$) iff $\mathrm{AltPath}(\vec x,\vec x_{-v})=(u_0,\dots,u_k)$ has even length $k\ge2$ with $u_k=w$:
--   $$w\text{ victim of }v\iff \exists\,(u_0=v,\dots,u_k)=\mathrm{AltPath}(\vec x,\vec x_{-v}),\ k\text{ even},\ k\ge2,\ u_k=w.$$
--   As a consequence, each blocker has a unique victim: if $w$ and $w'$ are both victims of $v$, then $w=w'$.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - encoding: the alternating path AltPath(x, x_{-v}) has even length k ≥ 2 with u_k = w → ∃ p, IsPathFrom (altPath G x v) v p ∧ Even (p.length - 1) ∧ 2 ≤ p.length - 1 ∧ p.getLast? = some w; reason: the path with u_0 = v of Lemma 4.1, as a vertex list
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 14, Fact 4.5

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_QueryCommit
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.5** (Unique Victim, p. 14). `v` has a victim `w` iff `AltPath(x, x_{-v})` has even
length `k ≥ 2` with `u_k = w`; consequently each blocker has a unique victim. -/
theorem fact_4_5 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (v : V) :
    (∀ w, IsVictim G x w v ↔
      ∃ p : List V, IsPathFrom (altPath G x v) v p ∧ Even (p.length - 1) ∧
        2 ≤ p.length - 1 ∧ p.getLast? = some w) ∧
    (∀ w w', IsVictim G x w v → IsVictim G x w' v → w = w') := by sorry

end RankingBeats.General
