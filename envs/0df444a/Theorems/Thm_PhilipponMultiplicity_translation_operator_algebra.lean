-- Prove2me | Theorems.Thm_PhilipponMultiplicity_translation_operator_algebra
-- name    : PhilipponMultiplicity.translation_operator_algebra
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T17:44:41.571025+00:00
-- url     : https://prove2.me/theorems/ec7a949d-ba24-4f41-97f7-89aaeb0791c6
-- title:
--   Linearity, multidegrees and order-zero specialization of translation operators
-- statement:
--   Let $K$ be a complete nontrivially normed field and let a translation chart have block degrees $c_i$. Every coefficientwise mixed differential operator is $K$-linear. If $P$ is multihomogeneous of degree $D$, its image is multihomogeneous of degree $(c_iD_i)_i$, including zero degrees and the zero polynomial. At order zero the operator is an actual $K$-algebra homomorphism: substitute the chart polynomials and evaluate their analytic coefficients at zero. These are the algebraic assertions immediately following Definition 4.1; chart existence and ideal comparison are separate questions.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, §4.1, printed pp. 371–374; https://numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity

theorem PhilipponMultiplicity.translation_operator_algebra
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K] :
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (order : ℕ)
        (directions : Fin order → Fin A.parameterDimension),
      (∀ (P Q : G.CoordinateRing) (a : K),
        polynomialOperator chart order directions (P + Q) =
          polynomialOperator chart order directions P + polynomialOperator chart order directions Q ∧
        polynomialOperator chart order directions (MvPolynomial.C a * P) =
          MvPolynomial.C a * polynomialOperator chart order directions P) ∧
      (∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
        G.ambient.IsHomogeneous P D →
        G.ambient.IsHomogeneous (polynomialOperator chart order directions P)
          (fun i => chart.degree i * D i))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (directions : Fin 0 → Fin A.parameterDimension),
      ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
        ∀ P, f P = polynomialOperator chart 0 directions P) := by sorry
