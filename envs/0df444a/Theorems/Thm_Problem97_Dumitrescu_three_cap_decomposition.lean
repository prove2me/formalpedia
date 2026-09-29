-- Prove2me | Theorems.Thm_Problem97_Dumitrescu_three_cap_decomposition
-- name    : Problem97.Dumitrescu.three_cap_decomposition
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:16:32.116788+00:00
-- url     : https://prove2.me/theorems/4dba05a7-7baa-40f6-9e99-0a6ced562a07
-- title:
--   Three-Cap Decomposition of the Circumscribed Branch
-- statement:
--   For a nonempty noncollinear convex-independent finite set and a circumscribed Moser triangle, there is a cap triple whose three cap cardinalities sum to the cardinality of the set plus three.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_Dumitrescu_three_cap_decomposition.lean#L1-L76

/- Generated theorem stub from Erdos9796Proof.P97.Dumitrescu.L4 by Stage 2 proof cut; source SHA-256 e83e9f54d8942578d2c5ed7d0655ace7578bc914fb411a46c1c9edcd9760b89a -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
open Problem97 Problem97.Dumitrescu



/-!
# Dumitrescu L4: three-cap decomposition (Problem 97)

`Problem97.Dumitrescu.three_cap_decomposition` packages the heavy
MEC + Moser-triangle + cap-partition machinery into the headline
combinatorial statement used downstream by Dumitrescu L5–L8:

  *From a convex-independent finite point set `A ⊆ ℝ²` and a Moser
  triangle on `A` in the **circumscribed branch** of the Sylvester
  dichotomy, one obtains a closed cap triple `C1, C2, C3 ⊆ A`
  satisfying the cap-sum identity*

    `|C1| + |C2| + |C3| = |A| + 3`.

This is a pure composition lemma — every load-bearing geometric step
is discharged by an existing proven theorem:

* `Problem97.MEC.moser_triangle_signed_area_ne_zero` discharges the
  Moser-nondegeneracy hypothesis `hMoserNonDeg` (`MoserNonDeg.lean`).
* `Problem97.MEC.arc_partition_count_eq_one` discharges the
  cap-count hypothesis `hAGenericCapCount` (`ArcPartitionCount.lean`).
* `Problem97.MEC.cap_partition_from_moser_circumscribed` assembles
  the `CapTriple` from those two pieces (`CapPartitionFromMEC.lean`).
* `Problem97.CapTriple.cap_sum_identity` gives the cap-sum identity
  (`CapStructure.lean`).

## Branch convention

L4 is stated **restricted to the circumscribed branch**: the
`hCircumscribed` hypothesis selects the left disjunct of the Sylvester
dichotomy (three pairwise distinct MEC-boundary vertices), matching the
existing `cap_partition_from_moser_circumscribed` shape. The diameter
branch (`Or.inr _`) is closed by a separate K4-driven exclusion lemma
(`p97-mec-no-diameter-under-k4`); consumers that need to handle a raw
Moser triangle case-split on `MT.case_split` themselves before invoking
`three_cap_decomposition`. Keeping L4 as a pure composition lemma keeps
the dependency chain L4 → {arc count, Moser non-degeneracy, cap-from-MEC,
cap-sum} clean and free of the K4 antecedent.

## References

* Adrian Dumitrescu (2006), *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Computational Geometry 36, 503–509. DOI: 10.1007/s00454-006-1262-y.
* Gabriel Nivasch, János Pach, Rom Pinchasi, and Shira Zerbib, *The Number of Distinct Distances from a Vertex of a Convex Polygon*, Journal of Computational Geometry 4 (2013), 1–12; arXiv:1207.1266 (2012 preprint).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

theorem Problem97.Dumitrescu.three_cap_decomposition
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (hConv : Problem97.ConvexIndep A)
    (MT : Problem97.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    ∃ CP : Problem97.CapTriple A (MT.toStructural hCircumscribed),
      CP.C1.card + CP.C2.card + CP.C3.card = A.card + 3 := by sorry
