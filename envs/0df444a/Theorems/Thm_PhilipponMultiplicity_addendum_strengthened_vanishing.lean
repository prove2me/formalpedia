-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_strengthened_vanishing
-- name    : PhilipponMultiplicity.addendum_strengthened_vanishing
-- status  : Disproved
-- author  : @tomasz
-- created : 2026-09-23T21:11:25.292306+00:00
-- url     : https://prove2.me/theorems/f52549fa-ecd8-4e82-9564-950090301fb4
-- title:
--   1987 addendum — sampled translates (positive dimension)
-- statement:
--   **Current disconnected-group formulation disproved (10 October 2026).** The additive line times a two-element group, with positive multidegree (1,1) and T=1, admits arbitrarily large samples satisfying the contact hypothesis. Three sampled points force any subgroup with all sampled translates in the zero set to be trivial, contradicting every proposed uniform Hilbert bound. Submission 47f50117-2eaa-4a18-a780-3ae26dcb545d proves the negation of the complete current statement. Connectedness or another source-faithful correction requires separate review and proof. The original formal statement is preserved.
--
--   Let $K$ be a Philippon base field. There are integers $c(E)\ge1$, depending only on the individual embedded commutative group factors, with the following property. Let $G=\prod_i E_i$ have positive dimension $n$, let $A$ be an analytic subgroup, let $\Sigma$ be a finite subset containing $0$, and let $P\ne0$ be multihomogeneous of degree $D$. If $P$ has contact at least $nT+1$ along $A$ at every point of $\Sigma(n)$, there is a connected algebraic subgroup $H$ incompletely defined in degrees at most $(c(E_i)D_i)_i$, such that
--   $$
--   \Sigma+H\subseteq Z(P)\cap G
--   $$
--   and, for $s=\operatorname{codim}_A(A\cap H)$,
--   $$
--   \binom{T+s}{s}\,| (\Sigma+H)/H |\,\mathcal H(H;D)
--   \le \mathcal H(G;(c(E_i)D_i)_i).
--   $$
--
--   This is the sampled-translates strengthening in [Philippon's 1987 addendum, p.398](https://numdam.org/articles/10.24033/bsmf.2084/). The formal statement retains the recorded $n>0$ correction; it is not presented as a verbatim hypothesis from the printed statement. Zero entries in $D$ and $T=0$ remain allowed.
--
--   **Formalization Note.** The earlier sketch (bbf2b376-2029-46dc-9fc0-10e35e5d5817) has been retired because its [pointed-isolation auxiliary](p2m:theorem/9522f00d-d75f-453b-8300-4c36fdf42090) was disproved. That counterexample concerns the stronger auxiliary construction and does not disprove this addendum. That retirement left the original addendum unresolved. The independent disconnected-group disproof recorded above now concerns the original addendum formulation itself; its formal statement is unchanged.
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

theorem addendum_strengthened_vanishing
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∀ g ∈ sample, translate g H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i)) := by sorry

end PhilipponMultiplicity
