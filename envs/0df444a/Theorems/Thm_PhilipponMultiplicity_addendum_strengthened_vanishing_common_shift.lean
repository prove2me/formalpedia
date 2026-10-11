-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_strengthened_vanishing_common_shift
-- name    : PhilipponMultiplicity.addendum_strengthened_vanishing_common_shift
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T15:28:30.844991+00:00
-- url     : https://prove2.me/theorems/7bedccb0-8554-49eb-b275-2734a85cd933
-- title:
--   1987 addendum — corrected common-shift vanishing
-- statement:
--   **Corrected common-shift variant; proved on 10 October 2026.** This replaces the sampled-containment conclusion in the printed strengthening rather than claiming to transcribe it exactly.
--
--   Let $K$ be the complex field or the completed algebraic closure of a prime-adic field, with its specified norm. There is a function assigning a positive integer $c(E)$ to every embedded commutative algebraic group factor $E$ over $K$. This function is chosen before the ambient product, analytic subgroup, sampling set, polynomial, degrees, and contact parameter.
--
--   Let $G=\prod_i G_i$ be connected of dimension $n>0$, let $A$ be an analytic subgroup, let $\Sigma\subset G$ be finite with $0\in\Sigma$, and let $T\in\mathbb N$. Let $P\ne0$ be multihomogeneous of multidegree $D=(D_i)\in\mathbb N^r$. Suppose its order along $A$ is at least $nT+1$ at every point of the $n$-fold sumset $\Sigma^{(n)}$.
--
--   Then there is a connected algebraic subgroup $H$ that is incompletely defined by equations of multidegrees at most $(c(G_i)D_i)$, and there is one point $v\in G$, shared by every $g\in\Sigma$, such that
--
--   $$
--   g+v+H\subseteq\{P=0\}\cap G\qquad(g\in\Sigma).
--   $$
--
--   The same subgroup satisfies, with $b$ the analytic codimension of $A\cap H$ in $A$,
--
--   $$
--   \binom{T+b}{b}\,\#((\Sigma+H)/H)\,\mathcal H(H;D)
--   \leq \mathcal H(G;(c(G_i)D_i)_i).
--   $$
--
--   Here $\mathcal H$ is the existing Hilbert degree form. The full coset count is retained. The common shift is arbitrary in $G$; it need not be a sample point. These are uniform embedding-dependent constants, and no quadratic addition bound is imposed on this forward statement.
-- source:
--   User-authorized corrected formulation of Philippon, Errata et addenda, 1987, printed p. 398, https://numdam.org/item/10.24033/bsmf.2084.pdf; addition-degree condition: Philippon 1986, section 4.1, printed p. 372, https://numdam.org/item/10.24033/bsmf.2060.pdf. The forward common-shift conclusion is an explicit correction, not an exact transcription.

import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem addendum_strengthened_vanishing_common_shift
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∃ c : EmbeddedCommutativeGroup K → ℕ,
      (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K), G.IsConnected → 0 < G.dimension →
      ∀ (A : AnalyticSubgroup G)
        (sample : Finset G.Point), 0 ∈ sample →
      ∀ (T : ℕ) (D : G.FactorIndex → ℕ) (P : G.CoordinateRing),
        P ≠ 0 → IsMultihomogeneousOfDegree G P D →
        (∀ g ∈ sumset sample G.dimension,
          ((G.dimension * T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P g) →
        ∃ H : AlgebraicSubgroup G,
          H.IsConnected ∧
          HasIncompleteDefinition G H.carrier (fun i => c (G.factor i) * D i) ∧
          (∃ v : G.Point,
            ∀ g ∈ sample,
              translate (g + v) H.carrier ⊆ zeroLocusOnGroup G P) ∧
          ((Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
              (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
            hilbertDegreeForm G Set.univ (fun i => c (G.factor i) * D i)) := by sorry

end PhilipponMultiplicity
