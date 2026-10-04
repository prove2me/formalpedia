-- Prove2me | Theorems.Thm_PhilipponMultiplicity_contact_order_condition_rank_bound
-- name    : PhilipponMultiplicity.contact_order_condition_rank_bound
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-02T04:01:36.081458+00:00
-- url     : https://prove2.me/theorems/56cdd0f6-e4d9-4cbf-8553-42cf82261f5a
-- title:
--   Rank bound on the contact-order jet-evaluation matrix (decomposition child of addendum_contact_hilbert_gap)
-- statement:
--   Decomposition child of PhilipponMultiplicity.addendum_contact_hilbert_gap: the contact-order condition as an explicit rank bound on the jet-evaluation matrix.
--
--   Let K be a Philippon base field, G an embedded product of commutative algebraic groups, and A an analytic subgroup. Let R be the K-submodule of the coordinate ring consisting of multihomogeneous polynomials of exact multidegree D (the space R_D), let T >= 0, and let `sample` be a finite set of points of G. Let E : R →ₗ[K] (ι → K) be the jet-evaluation matrix: each row is a jet datum at a sample point, and the kernel condition is that E P = 0 forces P to vanish to contact order at least T + 1 at every sample point (vanishingOrder A P g >= T + 1, the mission's contact-order predicate). If the row index type has at most |sample| * C(T + s, s) entries, then the K-rank of the image of E is at most |sample| * C(T + s, s).
--
--   In the intended instantiation s is the analytic codimension (analyticCodimension A H.carrier, as in the parent node's constant C(T + s, s) * |(Σ + H)/H| * H(H; D) ≤ H(G; D) / (4^n n!)), so this is the linear-algebra core of the parent's counting step: contact order ≥ T + 1 at a point imposes at most C(T + s, s) independent linear conditions on R_D. The bound is rank-nullity: finrank(range E) ≤ finrank(ι → K) = card ι.
-- source:
--   Decomposition child of PhilipponMultiplicity.addendum_contact_hilbert_gap (theorem 05d2413e-b689-4aac-913c-d368f113c785): the linear-algebra step of the converse addendum counting argument (Philippon 1987 addendum, sampled translates). The parent's per-point constant C(T + s, s) is isolated here as an explicit rank bound on the jet-evaluation matrix over the mission's Def_PhilipponMultiplicity_* definitions (vanishingOrder, IsMultihomogeneousOfDegree). Triage: ~/workspace/p2m_harness/philippon_triage.md § 'Publish-decomposition candidates' (1).

import Mathlib
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false

namespace PhilipponMultiplicity

/-- **Contact-order condition as a rank bound.** Let `R` be the space of
multihomogeneous coordinate polynomials of exact multidegree `D` on the
embedded group product `G` (a `K`-submodule of the coordinate ring), let
`sample` be a finite set of points, and let `E : R →ₗ[K] (ι → K)` be the
jet-evaluation matrix: its rows are the jet data at the sample points, and
`E P = 0` forces `P` to vanish to contact order at least `T + 1` at every
sample point (via the mission's `vanishingOrder`). If the row index type has
at most `|sample| * C(T + s, s)` entries -- the per-point jet count
`C(T + s, s)` times the number of sample points -- then the rank of `E` is at
most `|sample| * C(T + s, s)`. In the intended instantiation `s` is the
analytic codimension, so this is the linear-algebra core of the
`addendum_contact_hilbert_gap` counting step: contact order `≥ T + 1` at a
point imposes at most `C(T + s, s)` independent linear conditions on `R_D`. -/
theorem contact_order_condition_rank_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (T : ℕ) (D : G.FactorIndex → ℕ)
    (s : ℕ)
    (R : Submodule K G.CoordinateRing)
    (hR : ∀ P : G.CoordinateRing, P ∈ R → IsMultihomogeneousOfDegree G P D)
    (sample : Finset G.Point)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ sample.card * Nat.choose (T + s) s)
    (E : R →ₗ[K] (ι → K))
    (hE : ∀ P : R, E P = 0 →
      ∀ g ∈ sample, ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A (P : G.CoordinateRing) g) :
    Module.finrank K (LinearMap.range E) ≤ sample.card * Nat.choose (T + s) s := by sorry

end PhilipponMultiplicity
