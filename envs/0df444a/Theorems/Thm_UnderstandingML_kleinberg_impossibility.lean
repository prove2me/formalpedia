-- Prove2me | Theorems.Thm_UnderstandingML_kleinberg_impossibility
-- name    : UnderstandingML.kleinberg_impossibility
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:16:23.847447+00:00
-- url     : https://prove2.me/theorems/65b3714d-43b7-40f7-882e-78c789082d32
-- title:
--   Theorem 22.4 (Kleinberg): no clustering function on a domain with at least two points satisfies Scale Invariance, Richness and Consistency
-- statement:
--   **Theorem 22.4.** There exists no function, $F$, that satisfies all the three properties: Scale Invariance, Richness, and Consistency.
--
--   Formally: for a fixed finite domain $X$ with at least two points, no function from dissimilarities over $X$ to partitions of $X$ satisfies the three axioms. (The book's proof picks a domain with at least three points and uses only two of its partitions; dissimilarities are positive on distinct points, as in Kleinberg (2003), which the scaling step of the proof needs.)
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.5 p. 319, Theorem 22.4 with its proof (Kleinberg 2003)

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 22.4 (Kleinberg 2003)** (p. 319). There exists no function `F` that satisfies all
the three properties: Scale Invariance, Richness, and Consistency.
Stated for clustering functions on a fixed finite domain with at least two points (the
proof picks a domain with at least three points and uses two of its partitions). -/
theorem kleinberg_impossibility {X : Type*} [Fintype X] (hX : 2 ≤ Fintype.card X) :
    ¬ ∃ F : Dissimilarity X → Setoid X, ScaleInvariant F ∧ Rich F ∧ Consistent F := by sorry

end UnderstandingML
