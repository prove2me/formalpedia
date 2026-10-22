-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_pure_state_value_and_extensions
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.pure_state_value_and_extensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:27:01.024698+00:00
-- url     : https://prove2.me/theorems/5c7553eb-ddee-4535-ab0f-5686d590d11f
-- title:
--   Pure-state value and factorization of every extension
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $\psi\in\mathcal H_A\otimes\mathcal H_B$ be a unit vector and $\rho=|\psi\rangle\langle\psi|$. Every extension $\omega^{ABE}$ satisfies $$\omega=\rho\otimes\operatorname{Tr}_{AB}\omega,\qquad \tfrac12I(A;B|E)_\omega=S(\operatorname{Tr}_B\rho).$$ Consequently $$E_{\mathrm{sq}}(\rho)=S(\operatorname{Tr}_B\rho).$$ This fixes the pure-state normalization without introducing an independent entanglement functional.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 2, §II, Example 2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

/-- PDF p.2, Example 2: every extension factors, has the displayed half-CMI,
and the squashed value is exactly the entropy of the actual A marginal. -/
theorem pure_state_value_and_extensions
    (psi : EuclideanSpace ℂ (A × B)) (hpsi : ‖psi‖ = 1) :
    sq (pureDensity psi) = vnEntropy (traceRight (pureDensity psi)) ∧
    ∀ e : ℕ, 0 < e →
    ∀ omega : Matrix ((A × B) × Fin e) ((A × B) × Fin e) ℂ,
      IsDensityMatrix omega → traceRight omega = pureDensity psi →
      omega = Matrix.kronecker (pureDensity psi) (traceLeft omega) ∧
      cmi omega / 2 = vnEntropy (traceRight (pureDensity psi)) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
