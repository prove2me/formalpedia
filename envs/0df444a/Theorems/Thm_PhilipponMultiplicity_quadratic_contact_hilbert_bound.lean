-- Prove2me | Theorems.Thm_PhilipponMultiplicity_quadratic_contact_hilbert_bound
-- name    : PhilipponMultiplicity.quadratic_contact_hilbert_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T18:30:58.297747+00:00
-- url     : https://prove2.me/theorems/143cf775-f441-4a78-a05a-4762b313f1ad
-- title:
--   Sharp contact rank from quadratic addition laws
-- statement:
--   Let G be a connected product of embedded commutative algebraic groups over an algebraically closed, complete nontrivially normed field of characteristic zero. Assume each embedded factor admits local addition formulas of degree at most two in the first input; their second-input degrees need not be bounded. Let A be an analytic subgroup, H an algebraic subgroup (possibly disconnected), and g a point of G. Write b for the codimension of the tangent kernel of A along H.
--
--   For any multidegree D and nonnegative integer T, let J be an ideal whose homogeneous degree-D elements are precisely the polynomials having contact of order at least T+1 along A at every point of g+H. Then the actual quotient Hilbert functions satisfy
--
--   $$h_J(D)\leq\binom{T+b}{b}\,h_{I(H)}(2D).$$
--
--   The condition defining J specifies its degree-D contact equations; it does not assume a bound on their rank. The theorem needs neither a degree threshold nor connectedness of H. This is the geometric rank estimate used in the corrected quadratic-addition converse of Philippon's erratum.
-- source:
--   Supporting lemma for the corrected Philippon erratum converse. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, https://numdam.org/item/10.24033/bsmf.2060.pdf, section 4.1, printed p. 372 (bounded translated analytic coordinates); Philippon–Waldschmidt, https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/ProjectEuclid/IllinoisJM32-1988.pdf, proof of Lemma 6.7, printed pp. 304–306. This is a derived rank lemma, not an exact quotation.

import Definitions.Def_PhilipponMultiplicity_ErratumCorrections
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem quadratic_contact_hilbert_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (hadd : ∀ i, (G.factor i).HasAdditionDegreeAtMost 2)
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G) (g : G.Point)
    (T : ℕ) (D : G.FactorIndex → ℕ) (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) :
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D ≤
      Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) *
        Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
          (G.vanishingIdeal H.carrier) (fun i => 2 * D i) := by sorry

end PhilipponMultiplicity
