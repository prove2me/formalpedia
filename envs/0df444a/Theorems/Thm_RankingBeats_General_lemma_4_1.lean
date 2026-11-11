-- Prove2me | Theorems.Thm_RankingBeats_General_lemma_4_1
-- name    : RankingBeats.General.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:19.74723+00:00
-- url     : https://prove2.me/theorems/d101dc27-1884-4cff-87a0-5ef1b2d74d11
-- title:
--   Lemma 4.1 — Alternating Path Lemma: R^t(x) Δ R^t(x_{-v}) is a time-increasing alternating path from v
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix a vertex $v$ and a time $t\in[0,1)\times[0,1)$. Then $\mathrm{AltPath}^t(\vec x,\vec x_{-v})=(R^t(\vec x)\setminus R^t(\vec x_{-v}))\cup(R^t(\vec x_{-v})\setminus R^t(\vec x))$ is a path $p=(u_0,\dots,u_k)$ of distinct vertices such that
--   1. $u_0=v$;
--   2. for even $i$, $(u_i,u_{i+1})\in R^t(\vec x)$; for odd $i$, $(u_i,u_{i+1})\in R^t(\vec x_{-v})$;
--   3. for all $i\le k-2$, $t_{u_iu_{i+1}}<t_{u_{i+1}u_{i+2}}$, and consequently $x_{u_i}<x_{u_{i+2}}$;
--   4. for odd $k$, $A^t(\vec x_{-v})=A^t(\vec x)\cup\{u_k\}$; for even $k$, $A^t(\vec x)=A^t(\vec x_{-v})\cup\{u_k\}$.
--
--   $$\exists\,p=(u_0,\dots,u_k):\ \mathrm{AltPath}^t(\vec x,\vec x_{-v})=\{\{u_i,u_{i+1}\}\}_{i<k},\ u_0=v,\ \text{and 2.–4. hold.}$$
--   This is the central structural tool of the paper: removing or inserting one vertex changes Ranking's matching along a single path whose ranks increase along each parity class.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - encoding: AltPath^t is a path p = (u_0, ..., u_k) → ∃ p : List V with IsPathFrom (altPathAt G x v t) v p (distinct vertices, head v, edge set = consecutive pairs); u_i = p.getD i v, k = p.length - 1; reason: a path is determined by its vertex sequence; the head v fixes the orientation the paper uses
--   - encoding: R(x_{-S}): Ranking with the vertices of S removed → ranking G S x, the run with S unavailable from the start and the other ranks unchanged; reason: the paper's own description of removal (p. 12)
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 13, Lemma 4.1

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_QueryCommit

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Lemma 4.1** (Alternating Path Lemma, p. 13). For a rank vector `x`, a vertex `v` and a time
`t ∈ [0, 1) × [0, 1)`, `AltPath^t(x, x_{-v})` is a path `p = (u_0, …, u_k)` with `u_0 = v`;
its edges `(u_i, u_{i+1})` lie in `R_t(x)` for even `i` and in `R_t(x_{-v})` for odd `i`;
consecutive edges are queried in increasing time order, hence `x_{u_i} < x_{u_{i+2}}`; and the
available sets at time `t` differ only at `u_k`. -/
theorem lemma_4_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (v : V) (t : ℝ ×ₗ ℝ)
    (ht : (ofLex t).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (ofLex t).2 ∈ Set.Ico (0 : ℝ) 1) :
    ∃ p : List V, IsPathFrom (altPathAt G x v t) v p ∧
      (∀ i, i + 1 < p.length →
        (Even i → s(p.getD i v, p.getD (i + 1) v) ∈ partialRanking G ∅ x t) ∧
        (Odd i → s(p.getD i v, p.getD (i + 1) v) ∈ partialRanking G {v} x t)) ∧
      (∀ i, i + 2 < p.length →
        queryTime x (p.getD i v) (p.getD (i + 1) v) <
            queryTime x (p.getD (i + 1) v) (p.getD (i + 2) v) ∧
          x (p.getD i v) < x (p.getD (i + 2) v)) ∧
      (Odd (p.length - 1) →
        availableAt G {v} x t = insert (p.getD (p.length - 1) v) (availableAt G ∅ x t)) ∧
      (Even (p.length - 1) →
        availableAt G ∅ x t = insert (p.getD (p.length - 1) v) (availableAt G {v} x t)) := by sorry

end RankingBeats.General
