-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kOmega_iff_countableCompactHausdorffQuotient
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_iff_countableCompactHausdorffQuotient
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:29:09.32265+00:00
-- url     : https://prove2.me/theorems/edb52f63-e38b-4078-b2d8-d294707d5259
-- title:
--   Lemma C.2
-- statement:
--   Let $X$ be a topological space. Say that $X$ is k-omega when a countable covering family of continuous maps from compact Hausdorff spaces determines its final topology, as in Definition C.1. Then
--
--   $$X\text{ is k-omega}\quad\Longleftrightarrow\quad\exists\text{ a countable family }(K_i)_{i\in I}\text{ of compact Hausdorff spaces and a quotient map }\coprod_{i\in I}K_i\twoheadrightarrow X.$$
--
--   The coproduct is a topological disjoint union, and quotient maps are surjective with the quotient topology. Finite and empty families are included; $X$ itself need not be Hausdorff.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 38, Lemma C.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma C.2, PDF p. 38: precisely the countable coproduct quotient
characterization, retaining compact Hausdorff source spaces. -/
theorem kOmega_iff_countableCompactHausdorffQuotient
    (X : Type u) [TopologicalSpace X] :
    IsKOmega X ↔
      ∃ (I : Type u) (_ : Countable I) (K : I → CompHaus.{u})
        (q : (Σ i, K i) → X), IsQuotientMap q := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
