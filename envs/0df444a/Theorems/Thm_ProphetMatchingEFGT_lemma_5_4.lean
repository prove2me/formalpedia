-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_lemma_5_4
-- name    : ProphetMatchingEFGT.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:53.628035+00:00
-- url     : https://prove2.me/theorems/7c095718-1c12-4abf-a6c8-d2dea7c07141
-- title:
--   Lemma 5.4 — conditioning on '$j$ candidate of $u$' does not make $(ui)$ more likely to be active
-- statement:
--   Let $0\le c$, $x\in\mathcal F_M$, and consider the active-edge process of Algorithm 3 on a duplicate-free list of edges on which it is well defined. For all vertices $u,i,j$ with $i\ne j$,
--   $$\Pr_{\widetilde E_u,\pi_u}\big[(ui)\text{ is not active}\mid j\text{ candidate of }u\big]\ \ge\ \Pr_{\widetilde E_u}\big[(ui)\text{ is not active}\big],$$
--   stated as $\Pr[(ui)\text{ not active}]\cdot\Pr[j\text{ candidate of }u]\le\Pr[(ui)\text{ not active},\ j\text{ candidate of }u]$.
--
--   The lemma lets the conditional factors of eq. (13) be replaced by unconditional ones.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - encoding: Pr[(ui) not active | j candidate of u] → product form Pr[A, B] ≥ c·Pr[B] (or the corresponding product of probabilities); reason: the conditional probability is undefined on null events (slip 6); equal where it is defined
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
--   - reading: c is Algorithm 3's constant → 0 ≤ c; reason: a selection probability; all values of §5 are positive
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, Lemma 5.4, p. 15

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Lemma 5.4, p. 15.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Lemma 5.4, p. 15: "For all `u, i, j ∈ V` such that
`i ≠ j`, `Pr_{Ẽ_u, π_u}[(ui) is not active | j candidate of u] ≥ Pr_{Ẽ_u}[(ui) is not active]`."

**Formalization Note.** Product form: `Pr[(ui) not active] · Pr[j candidate of u] ≤
Pr[(ui) not active, j candidate of u]`. The active-edge process is that of Algorithm 3 on the edges
`es` (in arrival order), assumed well defined; `(ui)` is never active when it is not an edge of `es`. -/
theorem lemma_5_4 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc : 0 ≤ c) (x : Edge G → ℝ) (hx : InFM G x) (es : List (Edge G)) (hnd : es.Nodup)
    (hwd : WellDefinedOn c x es) (u i j : V) (hij : i ≠ j) :
    prob (actProbs c x es) (fun l => ¬ isActive l u i) *
        prob2 (actProbs c x es) (fun l l' => IsCandidate u l l' j) ≤
      prob2 (actProbs c x es) (fun l l' => ¬ isActive l u i ∧ IsCandidate u l l' j) := by sorry

end ProphetMatchingEFGT
