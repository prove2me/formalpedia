-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P83_deterministicChain
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P83.deterministicChain
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:19:11.382015+00:00
-- url     : https://prove2.me/theorems/956a6d3a-50b9-45cf-b903-4c992a36e8e2
-- title:
--   The complete deterministic and asymptotic comparison chain
-- statement:
--   Let $\rho$ be any normalized finite-dimensional bipartite state. Let $E_1$ be its exact one-copy PPT rate with real target size, $E_{\Gamma,0}$ the supremum of its positive-blocklength exact rate ratios, $E_\Gamma$ the PPT rate with fidelity tending to one, $E_W$ the logarithm of SDP (7), and $E_N$ its logarithmic negativity. Then
--
--   $$E_1(\rho)\le E_{\Gamma,0}(\rho)\le E_\Gamma(\rho)\le E_W(\rho)\le E_N(\rho).$$
--
--   All quantities are evaluated on the same state. The chain does not assert equality between deterministic and vanishing-error rates in general.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, PDF p. 5, Unnumbered result: complete deterministic/asymptotic comparison chain

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Complete five-term comparison chain, PDF p.5. All quantities refer
to the same normalized state and the exact one-copy target size is real. -/
theorem deterministicChain [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho) :
    oneCopyExact rho ≤ exactRegularized rho ∧
    exactRegularized rho ≤ entanglementGamma rho ∧
    entanglementGamma rho ≤ entanglementW rho ∧
    entanglementW rho ≤ entanglementN rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P83

end
