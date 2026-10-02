-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_converse
-- name    : PhilipponMultiplicity.addendum_converse
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T21:10:56.752072+00:00
-- url     : https://prove2.me/theorems/c86d0506-9d9d-4203-8b03-416dd74a15e2
-- title:
--   1987 addendum — converse construction (positive dimension)
-- statement:
--   For an embedded commutative group of positive dimension $n$, suppose $D_i\ge\mathcal H(G;1,\ldots,1)$ and an algebraic subgroup $H$ satisfies
--   $$
--   \binom{T+s}{s}|(\Sigma+H)/H|\mathcal H(H;D)
--   \le\frac{\mathcal H(G;D)}{4^n n!},
--   \qquad s=\operatorname{codim}_A(A\cap H).
--   $$
--   Then there is a polynomial of exact multidegree $D$, nonzero on $G$, with contact at least $T+1$ at every point of $\Sigma+H$.
--
--   An accepted proof-sketch proves the interpolation step using the actual finite-dimensional homogeneous spaces and the ideal of all sampled analytic jets. The remaining input is the [strict contact Hilbert-function gap](p2m:theorem/05d2413e-b689-4aac-913c-d368f113c785); this quantitative estimate is Open, so the converse is not yet proved. The subgroup need not be connected, and the original constant is retained.
--
--   Source: [Philippon's 1987 addendum, p. 398](https://numdam.org/articles/10.24033/bsmf.2084/). The explicit restriction $n>0$ is the mission's recorded correction for the zero-dimensional obstruction. The formal statement has not changed.
-- source:
--   1987, p. 398. https://numdam.org/articles/10.24033/bsmf.2084/

/-
Open statement draft. The proof and source-comparison obligations remain open.
This draft explicitly restricts the ambient group to positive dimension.
-/
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem addendum_converse
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D) :
    ∃ P : G.CoordinateRing,
      P ≠ 0 ∧ IsMultihomogeneousOfDegree G P D ∧
      (∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h)) ∧
      (∃ x : G.Point, x ∉ zeroLocusOnGroup G P) := by sorry

end PhilipponMultiplicity
