-- Prove2me | Theorems.Thm_TreeMultiflow_appendixB_precolour_extension
-- name    : TreeMultiflow.appendixB_precolour_extension
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:17.753053+00:00
-- url     : https://prove2.me/theorems/97eb66da-9d5d-4c87-8605-7e99641e351e
-- title:
--   Appendix B: precoloured edges extend to a proper 10-edge-colouring of a loopless multigraph of maximum degree six
-- statement:
--   In a loopless multigraph of maximum degree at most six, every proper partial edge colouring from a palette of ten colours extends to all edges if each vertex is incident to at most four precoloured edges.
--
--   That is, let $H$ be a finite multigraph without loops (parallel edges allowed) in which every vertex meets at most six edges. Let some edges be precoloured with colours from $\{1,\dots,10\}$ so that two distinct precoloured edges with a common endpoint have different colours, and suppose every vertex meets at most four precoloured edges. Then there is a colouring of all edges with the ten colours, agreeing with the precolouring, in which any two distinct edges with a common endpoint receive different colours.
--
--   This is the specialization of Edwards, Girão, van den Heuvel, Kang, Puleo and Sereni [EGH+18, Theorem 9] that the proof of Lemma 5.1 uses.
--
--   Differences from the source:
--   - encoding: a loopless multigraph → a finite edge type E with ends : E → Sym2 W and ¬(ends e).IsDiag; parallel edges are distinct elements of E; degree of v = #{e | v ∈ ends e}; reason: Lean convention; same multigraphs
--   - generalization: a finite multigraph → the vertex type W need not be finite (E is finite); reason: vertices meeting no edge impose no condition; the case of finite W is the paper's
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Appendix B, p.12 (proof of Lemma 5.1; specialization of [EGH+18, Theorem 9])

import Mathlib

namespace TreeMultiflow

/-- **Precolouring extension in multigraphs of maximum degree six (Appendix B).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Appendix B,
p.12, in the proof of Lemma 5.1: "We first record the specialization of Edwards, Girão, van den
Heuvel, Kang, Puleo, and Sereni [EGH+18, Theorem 9] that we need: in a loopless multigraph of
maximum degree at most six, every proper partial edge coloring from a palette of ten colors
extends to all edges if each vertex is incident to at most four precolored edges."

The multigraph has vertices `W` and a finite edge type `E`; edge `e` joins the two elements of
`ends e`. If no edge is a loop, every vertex meets at most six edges, the partial colouring `pre`
gives different colours to any two distinct precoloured edges sharing an endpoint, and every
vertex meets at most four precoloured edges, then there is a colouring `c : E → Fin 10` giving
different colours to any two distinct edges sharing an endpoint and agreeing with `pre` on the
precoloured edges.

**Formalization Note.** Parallel edges are distinct elements of `E` with the same `ends`; they
share both endpoints and so must get different colours. The degree of `v` is the number of edges
`e` with `v ∈ ends e` (loops are excluded). The vertex type need not be finite; only edges are
coloured. -/
theorem appendixB_precolour_extension {W E : Type*} [DecidableEq W] [Fintype E]
    (ends : E → Sym2 W) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (hdeg : ∀ v : W, (Finset.univ.filter fun e => v ∈ ends e).card ≤ 6)
    (pre : E → Option (Fin 10))
    (hproper : ∀ (e e' : E) (i j : Fin 10), e ≠ e' → (∃ v, v ∈ ends e ∧ v ∈ ends e') →
      pre e = some i → pre e' = some j → i ≠ j)
    (hpre : ∀ v : W, (Finset.univ.filter fun e => v ∈ ends e ∧ (pre e).isSome = true).card ≤ 4) :
    ∃ c : E → Fin 10,
      (∀ e e' : E, e ≠ e' → (∃ v, v ∈ ends e ∧ v ∈ ends e') → c e ≠ c e') ∧
      ∀ (e : E) (i : Fin 10), pre e = some i → c e = i := by sorry

end TreeMultiflow
