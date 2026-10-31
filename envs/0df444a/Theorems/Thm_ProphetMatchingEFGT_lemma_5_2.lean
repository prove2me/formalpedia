-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_lemma_5_2
-- name    : ProphetMatchingEFGT.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:54.2888+00:00
-- url     : https://prove2.me/theorems/a456af53-4d0a-4f51-a21d-21d59a22fc42
-- title:
--   Lemma 5.2 — $\Pr[u,v\text{ unmatched at }(uv)]\ge1-2c+\frac{c^2}{2}\left(\frac{1-2c}{1-c}\right)^2$
-- statement:
--   Let $0<c<\tfrac12$ and $x\in\mathcal F_M$. Let the edges of a duplicate-free list arrive, in order, before an edge $e=(uv)$ not in the list, and suppose Algorithm 3 is well defined on these earlier edges ($\alpha_{e'}\le1$, i.e. $c\le\Pr[\text{both ends of }e'\text{ unmatched at }e']$, for each of them). Then
--   $$\Pr[u,v\text{ are unmatched at }(uv)]\ \ge\ 1-2c+\frac{c^2}{2}\Big(\frac{1-2c}{1-c}\Big)^2.$$
--
--   With $c=0.337$ the right side is at least $c$, so $\alpha_{(uv)}\le1$ and the induction continues: this is the heart of Theorem 5.3.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - reading: c is Algorithm 3's constant (1/3 or 0.337 in §5) → 0 < c < 1/2; reason: the denominators 1 − c − cΣ ≥ 1 − 2c and (1 − 2c)/(1 − c) of §5.3 presuppose c < 1/2
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.2, Lemma 5.2, p. 14 (proof in §5.3, pp. 14–17)

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Lemma 5.2, p. 14.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Lemma 5.2, p. 14:
`Pr[u, v are unmatched at (uv)] ≥ 1 − 2c + (c²/2) · ((1 − 2c)/(1 − c))²`.

**Formalization Note.** For Algorithm 3 with constant `c ∈ (0, 1/2)` and marginals `x ∈ FM`; the edges
`es` arrive before `e = (uv)`, in this order. As in the proof (p. 14, "By the induction hypothesis, we
can assume that `α_e ≤ 1` for every edge `e ∈ E` but the last edge `(uv)`"), Algorithm 3 is assumed
well defined on `es`, in the form `c ≤ Pr[both ends of e' unmatched at e']` for each earlier `e'`. -/
theorem lemma_5_2 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (e : Edge G) (he : e ∉ es)
    (hwd : WellDefinedOn c x es) :
    1 - 2 * c + c ^ 2 / 2 * ((1 - 2 * c) / (1 - c)) ^ 2 ≤ unmatchedAt c x es e := by sorry

end ProphetMatchingEFGT
