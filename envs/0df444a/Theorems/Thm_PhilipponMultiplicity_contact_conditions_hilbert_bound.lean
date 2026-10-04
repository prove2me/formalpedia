-- Prove2me | Theorems.Thm_PhilipponMultiplicity_contact_conditions_hilbert_bound
-- name    : PhilipponMultiplicity.contact_conditions_hilbert_bound
-- status  : Disproved
-- author  : @junyihjy
-- created : 2026-10-03T00:11:56.603769+00:00
-- url     : https://prove2.me/theorems/2ca848f3-31cc-4cbd-a41e-39119b3e00cc
-- title:
--   Contact-conditions Hilbert-function bound for sampled cosets (decomposition child of addendum_contact_hilbert_gap)
-- statement:
--   Decomposition child of PhilipponMultiplicity.addendum_contact_hilbert_gap: the counting core of the contact-Hilbert gap. Let K be a Philippon base field, G an embedded product of commutative algebraic groups, and A an analytic subgroup. Let J be an ideal of the multihomogeneous coordinate ring cut out by contact conditions: a multihomogeneous polynomial P of exact multidegree D lies in J iff it vanishes to contact order at least T+1 (along A) at every point g+h with g in a finite sample and h in an algebraic subgroup H. Then the Hilbert function h_J(D) is at most C(T+s,s) * cosetCount(sample,H) * hilbertDegreeForm(G,H,D), where s is the analytic codimension of H: C(T+s,s) jet components per coset times the number of cosets met by the sample times the Hilbert degree form of H.
-- source:
--   Decomposition child of PhilipponMultiplicity.addendum_contact_hilbert_gap (theorem 05d2413e-b689-4aac-913c-d368f113c785): the counting core of the converse addendum (Philippon 1987 addendum, sampled translates). Decomposes the target into the contact-conditions Hilbert bound (this node) plus the degree-form bridge; sibling of the published-and-proved contact_order_condition_rank_bound (56cdd0f6). Spec: ~/workspace/p2m_harness/addendum_gap_decomposition_spec.md (Child A).

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

/-- **Contact-conditions Hilbert bound (counting core).** Let `J` be an ideal
of the multihomogeneous coordinate ring of the embedded group product `G`,
cut out by contact conditions: a multihomogeneous polynomial `P` of exact
multidegree `D` lies in `J` iff it vanishes to contact order at least `T + 1`
(along the analytic subgroup `A`) at every point `g + h` with `g` in the
finite sample and `h` in the algebraic subgroup `H`. Then the Hilbert function
of `J` at `D` is bounded by the number of jet conditions:
`C(T + s, s)` jet components per coset (with `s` the analytic codimension of
`H`), times the number of cosets of `H` met by the sample, times the
Hilbert degree form of `H` at `D`. This is the counting core of the
`addendum_contact_hilbert_gap` converse-addendum argument. -/
theorem contact_conditions_hilbert_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (H : AlgebraicSubgroup G)
    (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D : ℝ) ≤
      (Nat.choose (T + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier) : ℝ) *
        (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D := by sorry

end PhilipponMultiplicity
