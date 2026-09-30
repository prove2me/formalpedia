-- Prove2me | Theorems.Thm_PhilipponMultiplicity_projective_lift_contact_invariance
-- name    : PhilipponMultiplicity.projective_lift_contact_invariance
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-24T13:15:09.783184+00:00
-- url     : https://prove2.me/theorems/0f01c76b-4023-42ad-8a10-73b790287210
-- title:
--   Projective-lift invariance of analytic contact order
-- statement:
--   Over a Philippon base field (complex or p-adic complex), the contact order of a multihomogeneous polynomial along any translate of an analytic subgroup is independent of the chosen analytic homogeneous-coordinate lifts. The replacement lifts need only represent that translate on a neighborhood of the parameter origin. Orders are the infimum of the indices of nonzero iterated Frechet derivatives, including infinite order.
-- source:
--   Philippon (1986), p. 358: independence of analytic representatives and analytic codimension; https://numdam.org/articles/10.24033/bsmf.2060/. Granular foundation of the mission analytic_contact_invariance target.

import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators Topology
open Filter PhilipponMultiplicity

theorem PhilipponMultiplicity.projective_lift_contact_invariance (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : IsMultihomogeneousOfDegree G P D)
    (f : A.ParameterSpace → G.ambient.Variable → K)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) 0)
    (hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
          G.embedding (g + A.map ⟨z, hz⟩) i) :
    vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
      {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0}) := by sorry
