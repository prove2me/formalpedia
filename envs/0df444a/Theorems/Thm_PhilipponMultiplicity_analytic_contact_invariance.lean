-- Prove2me | Theorems.Thm_PhilipponMultiplicity_analytic_contact_invariance
-- name    : PhilipponMultiplicity.analytic_contact_invariance
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:33.951857+00:00
-- url     : https://prove2.me/theorems/8894fdbb-8bf8-44f5-b00b-7e12a0ddca59
-- title:
--   Sections 2 and 4 — intrinsic contact and transverse directions
-- statement:
--   **Compiled open theorem statement; proof not yet supplied.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Analytic homogeneous representatives give the same contact order. Analytic codimension is bounded by image dimension, is zero precisely for containment of the generated analytic subgroup, and admits a basis selected from coordinate directions.
-- source:
--   1986, pp.357–358,377–378. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology
open Filter

namespace PhilipponMultiplicity

theorem analytic_contact_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) :
    (∀ (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      IsMultihomogeneousOfDegree G P D →
      ∀ f : A.ParameterSpace → G.ambient.Variable → K,
        (∀ v, AnalyticAt K (fun z => f z v) 0) →
        (∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
          ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
            Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
              G.embedding (g + A.map ⟨z, hz⟩) i) →
        vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
          {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0})) ∧
    (∀ H : AlgebraicSubgroup G,
      analyticCodimension A H.carrier ≤ A.dimension ∧
      (analyticCodimension A H.carrier = 0 ↔ A.carrier ⊆ H.carrier) ∧
      ∃ directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension,
        IsTransverseCoordinateFamily A H directions) := by sorry

end PhilipponMultiplicity
