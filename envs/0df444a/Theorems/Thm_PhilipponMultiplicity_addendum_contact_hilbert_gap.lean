-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_contact_hilbert_gap
-- name    : PhilipponMultiplicity.addendum_contact_hilbert_gap
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T12:19:54.935193+00:00
-- url     : https://prove2.me/theorems/05d2413e-b689-4aac-913c-d368f113c785
-- title:
--   Strict contact Hilbert-function gap for the converse addendum
-- statement:
--   Let $K$ be a Philippon base field, $G$ an embedded product of commutative algebraic groups of dimension $n>0$, $A$ an analytic subgroup, and $\Sigma\subset G$ a finite set containing $0$. Let $T\ge0$, let $D$ be a vector of nonnegative integer block degrees, and let $H\subseteq G$ be an algebraic subgroup, not necessarily connected. Put $s=\operatorname{codim}_A(A\cap H)$. Assume
--   $$
--   D_i\ge\mathcal H(G;1,\ldots,1)\quad\text{for every }i,
--   \qquad
--   \binom{T+s}{s}|(\Sigma+H)/H|\mathcal H(H;D)
--   \le\frac{\mathcal H(G;D)}{4^n n!}.
--   $$
--   Write $R_D$ for the space of multihomogeneous coordinate polynomials of exact multidegree $D$. Suppose $J$ is an ideal of the coordinate polynomial ring such that, for every $P\in R_D$,
--   $$
--   P\in J\quad\Longleftrightarrow\quad
--   \operatorname{ord}_{A,g+h}(P)\ge T+1
--   \quad\text{for all }g\in\Sigma,\ h\in H.
--   $$
--   For any ideal $I$, set $h_I(D)=\dim_K\operatorname{im}(R_D\to R/I)$. Then the number of independent contact conditions is strictly smaller than the dimension of the polynomial sections on $G$:
--   $$
--   h_J(D)<h_{I(G)}(D).
--   $$
--   This is the quantitative Hilbert-function step in the converse construction. The strict inequality is the remaining numerical obligation; finite-dimensional interpolation then supplies a section satisfying all contact conditions and nonzero on $G$.
--
--   **Formalization Note.** Both dimensions are the existing quotient-piece Hilbert functions, not formal degree polynomials or assumed ranks. No homogeneity of $J$ is required; the dimensions only depend on its intersection with $R_D$. The degree and subgroup hypotheses, positive-dimensional restriction, and constant are exactly those of the mission's converse addendum. This coordinate-space formulation is an extracted intermediate statement, not a separately numbered assertion in the source.
-- source:
--   Philippon, Errata et addenda (1987), p. 398, final converse assertion, https://numdam.org/articles/10.24033/bsmf.2084/ . Coordinate-space formulation of the dimension comparison used to construct the polynomial. The cited linear-system method is in Philippon–Waldschmidt, Illinois J. Math. 32 (1988), Section 6(b)–(c), pp. 303–306, especially Lemma 6.7, https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/ProjectEuclid/IllinoisJM32-1988.pdf . Its specialized Serre-embedding estimate is not asserted to prove this exact general-embedding constant; that quantitative comparison remains Open.

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem addendum_contact_hilbert_gap
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D)
    (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) :
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D <
      Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D := by sorry

end PhilipponMultiplicity
