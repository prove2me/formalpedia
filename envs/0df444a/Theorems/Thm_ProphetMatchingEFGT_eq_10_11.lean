-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_10_11
-- name    : ProphetMatchingEFGT.eq_10_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:29.509384+00:00
-- url     : https://prove2.me/theorems/5db28a90-2048-4aa1-a651-5a8d8f4dd762
-- title:
--   Eqs. (10)–(11) — the inclusion–exclusion bound on $\Pr[u,v\text{ unmatched at }(uv)]$
-- statement:
--   Let $0\le c$, $x\in\mathcal F_M$, and let the edges of a duplicate-free list arrive before $e=(uv)$, which is not in the list; assume Algorithm 3 is well defined on them. With
--   $$x_u=\sum_{s\notin\{u,v\}}x_{us}\quad\text{and}\quad x_v=\sum_{s\notin\{u,v\}}x_{sv}$$
--   (sums over the earlier edges), the active-edge process satisfies:
--
--   1. $x_u\le1$ and $x_v\le1$;
--   2. $\Pr[u\text{ is matched at }(uv)]\le c\,x_u$ and $\Pr[v\text{ is matched at }(uv)]\le c\,x_v$ (eq. (10));
--   3. $\Pr[u,v\text{ unmatched at }(uv)]=1-\Pr[u\text{ matched}]-\Pr[v\text{ matched}]+\Pr[u,v\text{ matched}]$;
--   4. $\Pr[u,v\text{ unmatched at }(uv)]\ \ge\ 1-c\,(x_u+x_v)+\Pr[u,v\text{ are matched at }(uv)]$ (eq. (11)).
--
--   The union bound drops the last term and gives $c=1/3$; the improvement to $0.337$ comes from bounding that term from below.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
--   - reading: c is Algorithm 3's constant → 0 ≤ c; reason: a selection probability; all values of §5 are positive
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.2, eqs. (10)–(11) and the definition of x_u, x_v, p. 13

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Eqs. (10)–(11), p. 13: the inclusion–exclusion bound.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, eqs. (10)–(11), p. 13: with
`x_u = Σ_{s ∉ {u,v}} x_us ≤ 1` and `x_v = Σ_{s ∉ {u,v}} x_sv ≤ 1`,
`Pr[u is matched at (uv)] ≤ c · x_u`, `Pr[v is matched at (uv)] ≤ c · x_v`, and
`Pr[u, v unmatched at (uv)] = 1 − Pr[u matched] − Pr[v matched] + Pr[u, v matched]
≥ 1 − c · (x_u + x_v) + Pr[u, v are matched at (uv)]`.

**Formalization Note.** Probabilities are in the active-edge process of the edges `es` that arrive
before `e = (uv)` (the paper removes `(uv)` and later edges from `E`), and `x_us` is `0` for a pair
that is not an edge of `es` (`xPair`). Algorithm 3 is assumed well defined on `es`. -/
theorem eq_10_11 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (u v : V) (huv : (e : Sym2 V) = s(u, v))
    (hwd : WellDefinedOn c x es) :
    ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s ≤ 1 ∧
      ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es s v ≤ 1 ∧
      prob (actProbs c x es) (fun l => matchedIn l u) ≤
        c * ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s ∧
      prob (actProbs c x es) (fun l => matchedIn l v) ≤
        c * ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es s v ∧
      unmatchedAt c x es e = 1 - prob (actProbs c x es) (fun l => matchedIn l u)
        - prob (actProbs c x es) (fun l => matchedIn l v)
        + prob (actProbs c x es) (fun l => matchedIn l u ∧ matchedIn l v) ∧
      1 - c * (∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es u s
          + ∑ s ∈ univ.filter (fun s => s ≠ u ∧ s ≠ v), xPair x es s v)
        + prob (actProbs c x es) (fun l => matchedIn l u ∧ matchedIn l v) ≤ unmatchedAt c x es e := by sorry

end ProphetMatchingEFGT
