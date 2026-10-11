-- Prove2me | Theorems.Thm_PhilipponMultiplicity_closed_locus_has_hyperplane_hilbert_model
-- name    : PhilipponMultiplicity.closed_locus_has_hyperplane_hilbert_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-11T03:22:26.496003+00:00
-- url     : https://prove2.me/theorems/75e24766-419c-41c8-b28e-12cd9842e5c1
-- title:
--   Actual hyperplane Euler characteristic equals the original diagonal Hilbert function
-- statement:
--   Let K be an algebraically closed field, G an embedded commutative group product in the existing multiprojective formalization, and V a Zariski-closed subset of its projective closure. There exist a proper reduced K-scheme X, a homeomorphism from V onto all closed points of X, and an invertible sheaf L on X with a projective presentation whose morphism is a closed immersion. The topological Krull dimension of X is at most the original Hilbert-polynomial dimension of V. For all sufficiently large d, the Cech Euler characteristic of L to the d-th tensor power equals the original multigraded Hilbert function of the vanishing ideal of V at the diagonal multidegree (d,...,d), for every ordered affine cover. The Hilbert function and dimension are the existing concrete mission definitions. This is the diagonal geometric comparison needed in constructing the local-complex model; it does not assert a finitely generated numerical quotient or the full model.
-- source:
--   Philippon mission: geometric realization and diagonal Hilbert comparison for the local-complex frontier. Reuses the existing Proved Serre-vanishing, Cech comparison, section-surjectivity, and relevant-prime dimension results.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PhilipponMultiplicity_Support
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Topology
universe u

theorem PhilipponMultiplicity.closed_locus_has_hyperplane_hilbert_model
    (K : Type u) [Field K] [IsAlgClosed K] (G : EmbeddedGroupProduct K)
    (V : Set (groupProjectiveClosure G))
    (hV : @IsClosed _ (TopologicalSpace.induced Subtype.val G.ambient.zariskiTopology) V) :
    letI := G.ambient.zariskiTopology
    ∃ (X : Scheme.{u}) (π : X ⟶ Spec (.of K))
      (_ : V ≃ₜ {x : X | IsClosed {x}}) (L : X.Modules),
      IsProper π ∧ IsReduced X ∧
      topologicalKrullDim X ≤
        (SectionThree.locusDimension G.ambient (Subtype.val '' V) : WithBot ℕ∞) ∧
      Scheme.Modules.IsInvertible L ∧
      ∃ (N : ℕ) (p : L.ProjPresentation π N), IsClosedImmersion p.toProj ∧
        ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ U : X.OrderedAffineCover,
          (OModulePresheaf.ofModules π (L.tensorPow d)).eulerChar U =
            (Hilbert.hilbertFunction K G.ambient.factorCount G.ambient.ambientDimension
              (G.ambient.vanishingIdeal (Subtype.val '' V)) (fun _ => d) : ℤ) := by sorry
