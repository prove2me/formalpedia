-- Prove2me | Theorems.Thm_ResultantVNP_Supplement_theorem_1_7
-- name    : ResultantVNP.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:57:44.062861+00:00
-- url     : https://prove2.me/theorems/5f6e5db5-daee-4005-aded-a22c77d6a598
-- title:
--   Theorem 1.7 — the coefficient family $\{\Phi_{5m^2,m^2}(A)\}_{m\ge3}$ is VNP-complete under p-projections
-- statement:
--   Let $A$ be a generic symmetric tensor of order three, with one independent variable for each unordered triple of indices, and let $\Phi_{N,s}(A)=[z^s]\,\mathrm{Det}_N(I+zA)$. Then the family
--   $$\bigl\{\Phi_{5m^2,\,m^2}(A)\bigr\}_{m\ge3}$$
--   is **VNP-complete under p-projections over $\mathbb C$**:
--
--   1. it belongs to VNP, and
--   2. every VNP family is a p-projection of it, through members with index $m\ge3$.
--
--   The base mission poses the hardness half as Theorem 3.2. Together with membership it places the coefficient family among the complete families of Valiant's theory, alongside the permanent.
--
--   **Formalization Note** The resultant comes from an arbitrary resultant system, as in the base mission; by the uniqueness of the resultant all such systems agree. $\Phi$ is mapped from $\mathbb Z$ to $\mathbb C$.
--
--   Differences from the source:
--   - encoding: the family indexed by $m\ge3$ → member $n$ is $\Phi_{5(n+3)^2,(n+3)^2}$ for membership, and the index bound $3\le t(n)$ for hardness; reason: Lean polynomial families are indexed by all of $\mathbb N$; the same polynomials and the same polynomial bounds.
--   - encoding: "the resultant" → an arbitrary `ResultantSystem`; reason: all resultant systems agree with the unique resultant of Definition 2.1 in every case used.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.7, p.6

import Mathlib
import Definitions.Def_ResultantVNP_Supplement_coeffFamily
import Definitions.Def_ResultantVNP_IsVNPHardPProj

set_option autoImplicit false

namespace ResultantVNP

namespace Supplement

/-- **Theorem 1.7 (VNP-completeness of the coefficient family).** Let `A` be a generic symmetric
tensor of order three. The family `{Φ_{5m²,m²}(A)}_{m≥3}` is VNP-complete under p-projections over
`ℂ`: it lies in VNP, and every VNP family is a p-projection of it.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real
Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.7, p.6 (proof: Theorem 3.2, p.17, and Lemma A.1, p.38).

**Formalization Note** The resultant is taken from an arbitrary `ResultantSystem` `𝓡` (by the
uniqueness in Definition 2.1 it is the multivariate resultant). Membership is stated for
`coeffFamily 𝓡` (member `n` is `Φ_{5m²,m²}` with `m = n + 3`); hardness uses the base mission's
`IsVNPHardPProj` with the index bound `3`, as in Theorem 3.2. -/
theorem theorem_1_7 (𝓡 : ResultantSystem) :
    coeffFamily 𝓡 ∈ VNP ∧
      IsVNPHardPProj
        (fun m => MvPolynomial.map (Int.castRingHom ℂ) (charCoeff 𝓡 (5 * m ^ 2) (m ^ 2))) 3 := by sorry

end Supplement

end ResultantVNP
