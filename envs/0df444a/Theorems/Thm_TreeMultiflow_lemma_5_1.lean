-- Prove2me | Theorems.Thm_TreeMultiflow_lemma_5_1
-- name    : TreeMultiflow.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:01:17.763257+00:00
-- url     : https://prove2.me/theorems/b3c296e2-f584-41ef-8589-ff0aa9d3766e
-- title:
--   Lemma 5.1, existence part: completing a 10-colouring of the local paths of an attached star (time bound: lemma_5_1_polytime)
-- statement:
--   Consider the bins at the leaves of an attached star. Every bin contains at most six paths. Suppose the crossing paths have already been assigned colours from a set of ten colours, with distinct colours within each bin. Then all the local paths can be coloured using the same ten colours, without changing any crossing colour, so that the paths in each bin receive distinct colours, provided that either
--
--   1. (a) every bin contains at most four crossing paths; or
--   2. (b) there are at most six crossing paths altogether, and their colours are all different.
--
--   In the proof of Theorem 5.2 this lemma restores a contracted star with ten colours instead of eleven. This item is the existence part of Lemma 5.1; the polynomial-time part is the companion item `TreeMultiflow.lemma_5_1_polytime`.
--
--   **Formalization Note** The star enters only through its bins: each local path has its two ends in two different bins, each crossing path lies in one bin and carries its colour.
--
--   Differences from the source:
--   - generalization: the bins at the leaves of an attached star of a tree → an abstract finite family of local paths with two different bins and crossing paths with one bin and a colour (IsStarBinInstance); reason: every attached star yields such an instance with the same hypotheses and conclusion, and every such instance arises from a star with one bin per leaf
--   - encoding: a set of ten colours → Fin 10; reason: the colours are unnamed
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, pp.8–9

import Mathlib
import Definitions.Def_TreeMultiflow_IsStarBinInstance
import Definitions.Def_TreeMultiflow_IsBinColouringExtension

namespace TreeMultiflow

open Classical in
/-- **Lemma 5.1, existence: completing the colouring of a restored star.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
pp.8–9: "Consider the bins at the leaves of an attached star. Every bin contains at most six paths.
Suppose the crossing paths have already been assigned colors from a set of ten colors, with
distinct colors within each bin. We can color all the local paths using the same ten colors,
without changing any crossing color, provided that either (a) every bin contains at most four
crossing paths; or (b) there are at most six crossing paths altogether, and their colors are all
different. The resulting coloring gives distinct colors to the paths in each bin." The
polynomial-time part is `lemma_5_1_polytime`.

**Formalization Note.** The star is kept only through its bins (`IsStarBinInstance`): local
paths `L` with the bins `l₁ l ≠ l₂ l` of their two ends, crossing paths `C` with their bin `cb c`
and colour `κ c`. Case (a) bounds the crossing paths of every bin by four; case (b) bounds their
total number by six and asks `κ` to be injective. -/
theorem lemma_5_1 {B L C : Type*} [Fintype L] [Fintype C] (l₁ l₂ : L → B) (cb : C → B)
    (κ : C → Fin 10) (h : IsStarBinInstance l₁ l₂ cb κ)
    (hcase : (∀ β : B, (Finset.univ.filter fun c => cb c = β).card ≤ 4) ∨
      (Fintype.card C ≤ 6 ∧ Function.Injective κ)) :
    ∃ col : L → Fin 10, IsBinColouringExtension l₁ l₂ cb κ col := by sorry

end TreeMultiflow
