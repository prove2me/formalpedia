-- Prove2me | Theorems.Thm_SunMinCut_Cactus_lemma_2_5
-- name    : SunMinCut.Cactus.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T19:24:45.716171+00:00
-- url     : https://prove2.me/theorems/478477a6-03cd-4070-9d0a-5478500d2a4e
-- title:
--   Lemma 2.5 — height representation of the first-fit forests
-- statement:
--   Let $n\ge2$ and let a stream of edge copies (non-loop vertex pairs) be assigned by first fit to the forests $B_1,B_2,\dots$. Start with any spanning tree on $V$, possibly virtual, all edge heights zero. For an arriving copy $uv$, let $h$ be the smallest height on its current tree path, delete any path edge of height $h$ and insert the copy at height $h+1$. Then for every run of this process and after every prefix of the stream: for every $j\ge1$ the components of $B_j$ are exactly the components of the current tree edges of height at least $j$; the number $R$ of complete layers (forests $B_j$ that are spanning trees) is the minimum current height; and the complete layers form a prefix ($B_j$ is complete iff $j\le R$).
--
--   Differences from the source:
--   - encoding: "at every time" of the continuous-time arrival process → after every prefix of the stream of arrivals; reason: the forests and the tree change only at arrivals
--   - encoding: "delete any path edge of height h" → the conclusion holds for every run, i.e. for every choice of the deleted edge; reason: the lemma allows any choice
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, Lemma 2.5, p. 9

import Mathlib
import Definitions.Def_SunMinCut_Cactus_Processes

namespace SunMinCut.Cactus

/-- **Lemma 2.5 (Height representation)**, Sun 2026, doi:10.5281/zenodo.23915020, p. 9: start
with any spanning tree on `V` (possibly virtual) with all heights zero; for each arriving copy
`uv` let `h` be the smallest height on its current tree path, delete any path edge of height `h`
and insert the copy at height `h + 1`. Then after every prefix of the stream: the components of
each first-fit forest `B_j` are exactly those of the current tree edges of height at least `j`;
the number `R` of complete layers is the minimum current height; and the complete layers form a
prefix. -/
theorem lemma_2_5 (n : ℕ) (hn : 2 ≤ n) (arr : List (Sym2 (Fin n)))
    (harr : ∀ f ∈ arr, ¬ f.IsDiag) (states : ℕ → HTree n) (hrun : HRun arr states)
    (k : ℕ) (hk : k ≤ arr.length) :
    (∀ j, 1 ≤ j → ∀ x y : Fin n,
      (forestB (arr.take k) j).Reachable x y ↔ (heightAtLeast (states k) j).Reachable x y) ∧
    (∃ g ∈ (states k).T.edgeSet, (states k).ht g = completeCount (arr.take k) ∧
      ∀ g' ∈ (states k).T.edgeSet, (states k).ht g ≤ (states k).ht g') ∧
    ∀ j, 1 ≤ j → ((forestB (arr.take k) j).Connected ↔ j ≤ completeCount (arr.take k)) := by sorry

end SunMinCut.Cactus
