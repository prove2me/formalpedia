-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_12
-- name    : ProphetMatchingEFGT.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:30.166787+00:00
-- url     : https://prove2.me/theorems/2e45d067-63ea-4323-bc7e-c6ca29c9b59f
-- title:
--   Eq. (12) — $\Pr_{\widetilde E_u,\pi_u}[u^*\text{ candidate of }u]=c\,x_{uu^*}$
-- statement:
--   Let $0\le c$, $x\in\mathcal F_M$, and let the edges of a duplicate-free list arrive before $e=(uv)$, which is not in the list; assume Algorithm 3 is well defined on them. For the sampler $\pi_u$ (keep the activation $\widetilde E_u$ of the edges at $u$, resample all other edges independently, run greedy in arrival order, return the partner of $u$) and every vertex $u^*$,
--   $$\Pr_{\widetilde E_u,\pi_u}\big[u^*\text{ candidate of }u\big]=c\cdot x_{uu^*},$$
--   where $x_{uu^*}=0$ if $(uu^*)$ is not one of the earlier edges.
--
--   The candidate has the law of $u$'s partner in the actual run, which is what makes candidates useful as proposed witnesses.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
--   - reading: c is Algorithm 3's constant → 0 ≤ c; reason: a selection probability; all values of §5 are positive
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, eq. (12), p. 15 (sampler π_u defined on p. 14)

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Eq. (12), p. 15: the law of the candidate.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, eq. (12), p. 15:
`Pr_{Ẽ_u, π_u}[u* candidate of u] = c · x_uu*`.

**Formalization Note.** `π_u` (p. 14) keeps the true activation `Ẽ_u` of the edges at `u` (pattern
`l`), resamples the other edges independently with the same probabilities `α_e x_e` (pattern `l'`),
runs greedy in arrival order and returns `u`'s partner. The edges `es` arrive before `e = (uv)`; `x_uu*`
is `0` when `(uu*)` is not an edge of `es`. Algorithm 3 is assumed well defined on `es`. -/
theorem eq_12 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (u v : V) (huv : (e : Sym2 V) = s(u, v))
    (hwd : WellDefinedOn c x es) (ustar : V) :
    prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' ustar) = c * xPair x es u ustar := by sorry

end ProphetMatchingEFGT
