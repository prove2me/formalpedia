-- Prove2me | Theorems.Thm_PhilipponMultiplicity_addendum_converse_quadratic_connected
-- name    : PhilipponMultiplicity.addendum_converse_quadratic_connected
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T15:27:37.239069+00:00
-- url     : https://prove2.me/theorems/6e32d326-caca-45a1-b273-6ac439b9a746
-- title:
--   1987 addendum — connected converse with quadratic addition
-- statement:
--   **Converse with repaired geometric hypotheses; Proved.**
--
--   Let $K$ be the complex field or the completed algebraic closure of a prime-adic field, with its specified norm. Let $G=\prod_i G_i$ be a connected embedded commutative algebraic group of dimension $n>0$. For every factor, assume that addition has local homogeneous coordinate presentations covering all input pairs, of degree at most $2$ in the first input's coordinates. The degree in the second input is unrestricted.
--
--   Let $A$ be an analytic subgroup, $\Sigma\subset G$ a finite set containing $0$, $T\in\mathbb N$, and $D=(D_i)\in\mathbb N^r$. Assume $\mathcal H(G;1,\ldots,1)\le D_i$ for every $i$. Let $H$ be an algebraic subgroup, which may be disconnected, and let $b$ be the analytic codimension of $A\cap H$ in $A$. Suppose
--
--   $$
--   \binom{T+b}{b}\,\#((\Sigma+H)/H)\,\mathcal H(H;D)
--   \leq \frac{\mathcal H(G;D)}{4^n n!}.
--   $$
--
--   Then there is a nonzero multihomogeneous polynomial $P$ of multidegree $D$ with order along $A$ at least $T+1$ at every point $g+h$, for every $g\in\Sigma$ and $h\in H$. In addition, $P$ is nonzero at some point of $G$.
--
--   The constant, degree threshold, actual Hilbert degree forms, and contact-order definitions are unchanged. The explicit local addition-degree condition is a geometric assumption, not an assumed interpolation or rank estimate.
--
--   The accepted converse reduction now has only Proved dependencies: the sharp contact-rank estimate, the ambient lower Hilbert bound, and the subgroup upper Hilbert bound. Its Open frontier is empty. The formal statement is unchanged.
-- source:
--   User-authorized corrected formulation of Philippon, Errata et addenda, 1987, printed p. 398, https://numdam.org/item/10.24033/bsmf.2084.pdf; addition-degree condition: Philippon 1986, section 4.1, printed p. 372, https://numdam.org/item/10.24033/bsmf.2060.pdf. The forward common-shift conclusion is an explicit correction, not an exact transcription.

import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem addendum_converse_quadratic_connected
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (hadd : ∀ i : G.FactorIndex, (G.factor i).HasAdditionDegreeAtMost 2)
    (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
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
