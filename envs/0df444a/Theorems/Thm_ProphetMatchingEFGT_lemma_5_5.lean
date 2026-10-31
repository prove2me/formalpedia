-- Prove2me | Theorems.Thm_ProphetMatchingEFGT_lemma_5_5
-- name    : ProphetMatchingEFGT.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:01.63107+00:00
-- url     : https://prove2.me/theorems/5a405a9a-f4e0-4c07-a8f2-48232d6ea0c3
-- title:
--   Lemma 5.5 — a vertex has no active edge with probability at least $\frac{1-2c}{1-c}$
-- statement:
--   Let $0<c<\tfrac12$, $x\in\mathcal F_M$, and consider the active-edge process of Algorithm 3 on a duplicate-free list of edges on which it is well defined. For every vertex $r$,
--   $$\Pr_{\widetilde E_r}\big[(rs)\text{ is not active }\forall s\big]\ \ge\ \frac{1-2c}{1-c}.$$
--
--   It bounds the last factor of eq. (13) and the probability that a candidate is a witness.
--
--   Differences from the source:
--   - encoding: probabilities of Algorithm 3 (realization of R and the coin with probability α) → probabilities in the active-edge process of p.14 (each earlier edge active independently with probability α_e x_e, active edges picked greedily in arrival order), computed as finite sums; reason: the page's own unification ('For the purpose of analysis…', p.14); same law whenever α_e ≤ 1
--   - reading: the induction hypothesis 'α_e ≤ 1 for every edge e ∈ E but the last edge (uv)' (p.14), left implicit in the statement → hypothesis WellDefinedOn c x es: c ≤ Pr[both ends of e' unmatched at e'] for every earlier edge e'; reason: the statement is made inside this induction; the form c ≤ Pr[…] avoids the junk value α = c/0 = 0
--   - reading: c is Algorithm 3's constant (1/3 or 0.337 in §5) → 0 < c < 1/2; reason: the denominators 1 − c − cΣ ≥ 1 − 2c and (1 − 2c)/(1 − c) of §5.3 presuppose c < 1/2
--   - encoding: x ∈ FM (§5, p.12) → InFM G x on the edges of the simple graph G; reason: same polytope (p.10)
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5.3, Lemma 5.5, p. 16

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_ActiveProcess

open Finset

namespace ProphetMatchingEFGT

/-- **Lemma 5.5, p. 16.**
Ezra–Feldman–Gravin–Tang, arXiv:2002.09807v2, Lemma 5.5, p. 16: "For any vertex `r`,
`Pr_{Ẽ_r}[(rs) is not active ∀ s] ≥ (1 − 2c)/(1 − c)`."

**Formalization Note.** The active-edge process of Algorithm 3 with constant `c ∈ (0, 1/2)` on the
edges `es` (in arrival order, the paper's `E` with `(uv)` removed), assumed well defined. -/
theorem lemma_5_5 {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : ℝ) (hc0 : 0 < c) (hc : c < 1 / 2) (x : Edge G → ℝ) (hx : InFM G x)
    (es : List (Edge G)) (hnd : es.Nodup) (hwd : WellDefinedOn c x es) (r : V) :
    (1 - 2 * c) / (1 - c) ≤ prob (actProbs c x es) (fun l => ∀ s : V, ¬ isActive l r s) := by sorry

end ProphetMatchingEFGT
