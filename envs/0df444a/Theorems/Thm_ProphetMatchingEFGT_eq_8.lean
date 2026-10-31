-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_eq_8
-- name    : ProphetMatchingEFGT.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:10.877644+00:00
-- url     : https://prove2.me/theorems/a94e0ef3-1b0c-4478-92e3-a37fa23abbe7
-- title:
--   Eq. (8) — Algorithm 3 matches a realized edge with probability exactly $c$
-- statement:
--   Let $0\le c$, $x\in\mathcal F_M$, and let the edges of a duplicate-free list arrive, in order, before an edge $e=(uv)$ not in the list. Suppose Algorithm 3 is well defined on these edges and at $e$. Then, in the active-edge process,
--   $$\Pr[e\text{ is matched}]=\Pr[u,v\text{ are unmatched at }e]\cdot\alpha_e\cdot x_e\quad\text{and}\quad\Pr[u,v\text{ are unmatched at }e]\cdot\alpha_e=c,$$
--   with $\alpha_e=c/\Pr[u,v\text{ are unmatched at }e]$ (eq. (7)). Since $\Pr[e\in R_e]=x_e$, this is
--   $$\Pr\big[(uv)\text{ is matched}\mid(uv)\in R_{(uv)}\big]=\Pr[u,v\text{ are unmatched at }(uv)]\cdot\alpha_{(uv)}=c.$$
--
--   It shows that a well-defined Algorithm 3 is a $c$-selectable OCRS, with equality.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - encoding: Pr[(uv) matched | (uv) ∈ R_(uv)] (conditioning on realization, probability x_e) → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - reading: (8) presupposes α_e ≤ 1 for this and every earlier edge ('It remains to show that Algorithm 3 is well-defined', p.12) → WellDefinedOn c x (es ++ [e]); reason: the matching probability α must be a probability; c ≤ Pr[…] avoids the junk value c/0
--   - encoding: E with (uv) and the later edges removed (p.14), in the order σ → a duplicate-free list es of the edges arriving before e = (uv), e ∉ es; x_us := 0 when (us) is not in es; reason: an arrival order restricted to the prefix; x restricted to the prefix stays in FM
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
--   - reading: c is Algorithm 3's constant → 0 ≤ c; reason: a selection probability; all values of §5 are positive
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5, eq. (8) (with eq. (7)), p. 12

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Eq. (8), p. 12: Algorithm 3 matches a realized edge with probability exactly `c`.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, eq. (8), p. 12:
`Pr[(uv) is matched | (uv) ∈ R_(uv)] = Pr[u, v are unmatched at (uv)] · α_(uv) = c`.

**Formalization Note.** Stated in the active-edge process of p. 14 (`e` active with probability
`α_e x_e`), in product form: `Pr[e matched] = Pr[u, v unmatched at e] · α_e · x_e` and
`Pr[u, v unmatched at e] · α_e = c`, with `α_e = c / Pr[u, v unmatched at e]` (eq. (7)). The edges
`es` arrive before `e`, in this order; Algorithm 3 is assumed well defined (`α ≤ 1`, in the form
`c ≤ Pr[…]`) on `es` and at `e`. -/
theorem eq_8 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (e : Edge G) (he : e ∉ es) (hwd : WellDefinedOn c x (es ++ [e])) :
    prob (actProbs c x (es ++ [e])) (fun l => e ∈ greedy l)
        = unmatchedAt c x es e * (c / unmatchedAt c x es e) * x e ∧
      unmatchedAt c x es e * (c / unmatchedAt c x es e) = c := by sorry

end ProphetMatchingEFGT
