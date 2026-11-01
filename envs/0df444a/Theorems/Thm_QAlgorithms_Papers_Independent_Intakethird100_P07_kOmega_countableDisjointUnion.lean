-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kOmega_countableDisjointUnion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kOmega_countableDisjointUnion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:30:02.473865+00:00
-- url     : https://prove2.me/theorems/fd9d2d2c-cd76-43f0-b5f1-54fc15f11328
-- title:
--   Lemma C.4
-- statement:
--   Let $I$ be an at most countable set and $(X_i)_{i\in I}$ a family of k-omega spaces, with the meaning of Definition C.1. Then
--
--   $$\coprod_{i\in I}X_i\text{ is k-omega}.$$
--
--   The coproduct carries the disjoint-union topology. Finite families and the empty family are included, and the spaces need not be Hausdorff.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 38, Lemma C.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- Lemma C.4, PDF p. 38: countable disjoint unions, including finite
and empty ones, preserve the source's k-omega condition. -/
theorem kOmega_countableDisjointUnion
    (I : Type u) [Countable I] (X : I → Type u)
    [∀ i, TopologicalSpace (X i)] (hX : ∀ i, IsKOmega (X i)) :
    IsKOmega (Σ i, X i) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
