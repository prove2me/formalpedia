-- Prove2me | Theorems.Thm_PhilipponMultiplicity_retained_polynomial_operator_ideal_laws
-- name    : PhilipponMultiplicity.retained_polynomial_operator_ideal_laws
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T17:44:48.20952+00:00
-- url     : https://prove2.me/theorems/78eef52b-4dc2-4e54-ac04-44cf6fc654a3
-- title:
--   Monotonicity and sums of retained polynomial differential ideals
-- statement:
--   For a supplied translation atlas, order bound $T$, and multihomogeneous ideals $I,J$, let $\delta^T I$ denote the polynomial-operator ideal followed by retention at all homogeneous representatives of group points. Then $I\subseteq J$ implies $\delta^T I\subseteq\delta^T J$, and
--   $$\delta^T(I+J)=\operatorname{Ret}_G(\delta^T I+\delta^T J).$$
--   This is equality of actual ideals. Localization, contraction and intersections retain scheme multiplicities; no radical or zero-locus replacement is used. The statement holds over every complete nontrivially normed field. It formalizes the ideal laws stated after Definition 4.2.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §4.1, printed pp. 371–374; https://numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity

theorem PhilipponMultiplicity.retained_polynomial_operator_ideal_laws
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I J : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (hJ : IsMultihomogeneousIdeal G.ambient J) :
    (I ≤ J → retainedPolynomialOperatorIdeal atlas T I ≤
      retainedPolynomialOperatorIdeal atlas T J) ∧
    (retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
      retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
        retainedPolynomialOperatorIdeal atlas T J)) := by sorry
