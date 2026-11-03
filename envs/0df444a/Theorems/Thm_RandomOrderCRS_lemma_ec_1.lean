-- Prove2me | Theorems.Thm_RandomOrderCRS_lemma_ec_1
-- name    : RandomOrderCRS.lemma_ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:01.618414+00:00
-- url     : https://prove2.me/theorems/e2dfbfbf-fc47-4d90-84c9-9d6e82ce744b
-- title:
--   Lemma EC.1 — reduction to 1-regular inputs
-- statement:
--   Let $G=(V,E)$ be a finite graph with fractional matching $x$, and let $(G',x')$ be the 7-cycle construction. Then:
--
--   1. $(G',x')$ is explicit, with $|V'|=7|V|$ and $|E'|=|E|+7|V|$;
--   2. $(G',x')$ is 1-regular;
--   3. if $G$ has no cycles of length 3 or 5, then neither does $G'$;
--   4. for every $\alpha$: if there is an $\alpha$-selectable RCRS (respectively OCRS) for $(G',x')$, then there is an $\alpha$-selectable RCRS (respectively OCRS) for $(G,x)$.
--
--   This is the long form of Lemma 1. It lets the analysis of §3 assume 1-regularity, and with Theorem 3 it gives the guarantee for every input.
--
--   Differences from the source:
--   - generalization: there exist $G'$ and $x'$ → the statement is about the concrete `regularize` and `regularizeX` of the proof on ec14; reason: it names the witness, so it implies the existential statement
--   - reading: $(G',x')$ can be computed in time polynomial in the size of $(G,x)$ → an explicit definition with $|V'|=7|V|$ and $|E'|=|E|+7|V|$; reason: there is no running-time notion in this development, and the sizes are what the paper's remark uses
--   - reading: the simulation on ec15 may reuse the real arrival times → a `Policy` sees only the order and the states, so the seed must carry its own interleaving; reason: this is the stronger of the two readings of the model on p.3 and ec15
--   - encoding: a sequential scheme with a uniformly random order → `Policy` (finite seed, decision on history, current edge and state), `run`, and the average of `selProb` over all $|E|!$ orders; reason: finite seeds lose no generality, since a scheme is a mixture of finitely many deterministic rules
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Lemma EC.1, ec14; construction, ec14; Lemma 1, p.17

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Policy
import Definitions.Def_RandomOrderCRS_Regularize

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma EC.1 (Reduction to 1-Regular Inputs – Long Version), MacRury, Ma & Grammel,
arXiv:2209.07520v2, Appendix C.1, ec14; Lemma 1, p.17, is its short form. For the concrete
construction of ec14:
1. `(G′, x′)` is explicit, with `|V′| = 7|V|` and `|E′| = |E| + 7|V|`;
2. `(G′, x′)` is 1-regular;
3. if `G` has no cycles of length 3 or 5, then neither does `G′`;
4. an `α`-selectable RCRS (respectively OCRS) for `(G′, x′)` gives one for `(G, x)`.

**Formalization Note.** Clause 1 reads "computed in time polynomial in the size of (G, x)" as an
explicit definition with these sizes. The schemes see only orders and states, so in clause 4 the
scheme for `G` must draw its own interleaving of the gadget edges with its seed, rather than reuse
arrival times as on ec15. -/
theorem lemma_ec_1 (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (hx : IsFractionalMatching G x) :
    (Fintype.card (V × Fin 7) = 7 * Fintype.card V ∧
      Fintype.card (regularize G).edgeSet = Fintype.card G.edgeSet + 7 * Fintype.card V) ∧
    IsOneRegular (regularize G) (regularizeX G x) ∧
    (NoCyclesOfLengthThreeOrFive G → NoCyclesOfLengthThreeOrFive (regularize G)) ∧
    ∀ α : ℝ,
      ((∃ π' : Policy (regularize G), IsRCRSelectable (regularize G) π' (regularizeX G x) α) →
        ∃ π : Policy G, IsRCRSelectable G π x α) ∧
      ((∃ π' : Policy (regularize G), IsOCRSelectable (regularize G) π' (regularizeX G x) α) →
        ∃ π : Policy G, IsOCRSelectable G π x α) := by sorry

end RandomOrderCRS
