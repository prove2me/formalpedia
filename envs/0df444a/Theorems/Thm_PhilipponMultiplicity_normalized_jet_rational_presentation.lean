-- Prove2me | Theorems.Thm_PhilipponMultiplicity_normalized_jet_rational_presentation
-- name    : PhilipponMultiplicity.normalized_jet_rational_presentation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T06:40:12.942582+00:00
-- url     : https://prove2.me/theorems/2485f746-3ed9-4b59-8089-e222a8b8b88b
-- title:
--   Normalized jets have regular homogeneous fractions with operator-ideal numerators
-- statement:
--   Let $K$ be a complete nontrivially normed field, $G$ an embedded group product, $A$ an analytic subgroup, $g$ a translation point, and $\mathcal T$ a polynomial translation atlas. Fix an ideal $I$, a nonnegative integer $T$, a multihomogeneous polynomial $P\in I$, target pivots $b$, and an ordered derivative $j$ of order at most $T$. Write $J_T$ for the polynomial-operator ideal and $H_{P,b,j}$ for the normalized analytic jet.
--
--   At every point $x$ for which $g+x$ belongs to the target coordinate chart, there are a Zariski-open neighborhood $U$ of $x$ and multihomogeneous polynomials $N,D_0$ of the same multidegree such that
--
--   $$
--   N\in J_T,\qquad D_0(y)\ne0,\qquad H_{P,b,j}(y)=\frac{N(y)}{D_0(y)}\quad(y\in U).
--   $$
--
--   The numerator belongs to the actual operator ideal, so this statement preserves multiplicities. It supplies the regular rational coefficients needed for the coordinate-ratio comparison in Proposition 4.3. The ideal $I$ need not itself be multihomogeneous.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Definition 4.2 and the coordinate-ratio/Leibniz argument in the proof of Proposition 4.3, printed pp. 373–374; https://numdam.org/articles/10.24033/bsmf.2060/ . This is a supporting comparison lemma for the intrinsic local-jet formalization.

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity

theorem PhilipponMultiplicity.normalized_jet_rational_presentation
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing)
    (P : G.CoordinateRing) (hPI : P ∈ I) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D) (b : CoordinateChart G)
    (j : JetIndex A.parameterDimension T) (x : G.Point)
    (hx : g+x ∈ chartDomain G b) :
    ∃ U : Set G.Point, @IsOpen _ G.zariskiTopology U ∧ x ∈ U ∧
      ∃ r : RationalCoefficient G, r.numerator ∈ polynomialOperatorIdeal atlas T I ∧
        ∀ y ∈ U, G.ambient.eval r.denominator (G.embedding y) ≠ 0 ∧
          r.value y = normalizedJet A g b P j y := by sorry
