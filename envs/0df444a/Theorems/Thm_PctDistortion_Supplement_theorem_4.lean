-- Prove2me | Theorems.Thm_PctDistortion_Supplement_theorem_4
-- name    : PctDistortion.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:30:12.13491+00:00
-- url     : https://prove2.me/theorems/63029228-47d0-48a2-bf00-11f204764295
-- title:
--   Theorem 4 — 3/2-approximate Caccetta–Häggkvist: an oriented digraph of girth $g$ has a node of in-degree $< \tfrac32|V|/g$
-- statement:
--   Let $G=(V,E)$ be an oriented digraph (no loops and no 2-cycles) on a finite node set, with finite girth $g=g(G)$. Then $G$ has a node $j\in V$ with
--   $$\deg^-(j)<\frac32\cdot\frac{|V|}{g}.$$
--
--   The Caccetta–Häggkvist conjecture asks for the same bound without the factor $3/2$ and with $g-1$ in place of $g$; this theorem is an unconditional approximation of it, and through Theorem 5 it gives the unconditional distortion bound of Theorem 6.
--
--   Differences from the source:
--   - encoding: finite girth g = g(G) → IsGirth G g: a directed cycle (published Digraph.HasCycleOfLength) of length g ≥ 1 and none of any length 1 ≤ ℓ < g; reason: the paper's definition of girth as the shortest directed cycle length; lengths start at 1 because HasCycleOfLength 0 is vacuous
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 4, p.19 (= Theorem C, p.5)

import Mathlib
import Definitions.Def_PctDistortion_inDeg
import Definitions.Def_PctDistortion_Supplement_IsGirth

set_option autoImplicit false

namespace PctDistortion.Supplement

open PctDistortion

/-- **Theorem 4** (3/2-Approximate Caccetta-Häggkvist). Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Theorem 4, p.19 (= Theorem C, p.5):
"Every oriented digraph G = (V, E) with finite girth g = g(G) has a node j ∈ V with in-degree
deg−(j) < 3/2 · |V|/g."

**Formalization Note.** `G` is a digraph on a finite node type; "oriented" is the published
`IsOriented` (no loops, no 2-cycles) and "finite girth `g`" is `IsGirth G g` (a shortest directed
cycle has length `g`). The inequality is strict and in `ℝ`. -/
theorem theorem_4 {W : Type} [Fintype W] (G : Digraph W) (g : ℕ) (hG : IsOriented G)
    (hg : IsGirth G g) :
    ∃ j : W, (inDeg G j : ℝ) < 3 / 2 * ((Fintype.card W : ℝ) / (g : ℝ)) := by sorry

end PctDistortion.Supplement
