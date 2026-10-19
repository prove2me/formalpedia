-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P33_separableIntegral
-- name    : QAlgorithms.Papers.Independent.Dependency50.P33.separableIntegral
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:19:17.731433+00:00
-- url     : https://prove2.me/theorems/0b2730a0-85af-47c9-9660-045feeb7951c
-- title:
--   Separable states are precisely probability mixtures of product states
-- statement:
--   Let $H$ and $K$ be nonzero separable complex Hilbert spaces, and let $\mathfrak S(H)$ denote the density operators on $H$, equipped with the trace-norm Borel structure. Their tensor product is the completed Hilbert tensor product. A density operator $\rho$ on $H\otimes K$ is separable when it belongs to the trace-norm closed convex hull of all product density operators. Then $\rho$ is separable if and only if a Borel probability measure $\mu$ on $\mathfrak S(H)\times\mathfrak S(K)$ satisfies
--
--   $$
--   \rho=\int_{\mathfrak S(H)\times\mathfrak S(K)}\alpha\otimes\beta\,\mu(d\alpha,d\beta).
--   $$
--
--   The integral is the trace-class Bochner integral. The measure may have uncountable support. This characterization replaces finite convex combinations by probability ensembles in infinite dimensions.
--
--   **Formalization Note** Countable orthonormal coordinates identify each Hilbert space with a complete complex $\ell^2$ space. The coefficient identities and explicit integrability in Lean characterize the Bochner integral uniquely.
-- source:
--   Separability and Entanglement-Breaking in Infinite Dimensions, arXiv:quant-ph/0504204v1, PDF p. 2, §2, equation (2)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.RealRegisters (Hilbert)

/-- Integral representation (2), PDF pp.2–3 after Definition 1.
The Borel probability measure need not be atomic. -/
theorem separableIntegral {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] (rho : State (I × J)) :
    IsSeparable rho.coefficients ↔
      ∃ mu : Measure (State I × State J), IsProbabilityMeasure mu ∧
        IsBarycenter mu
          (fun p => productCoeff p.1.coefficients p.2.coefficients) rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P33

end
