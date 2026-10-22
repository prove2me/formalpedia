-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_superadditivity_and_additivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.superadditivity_and_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:26:09.976001+00:00
-- url     : https://prove2.me/theorems/c0f13571-9ea4-4a97-b356-780932f2b7ab
-- title:
--   Superadditivity and tensor-product additivity
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   For every state $\omega^{AA\prime BB\prime}$, let $\rho^{AB}=\operatorname{Tr}_{A\prime B\prime}\omega$ and $\sigma^{A\prime B\prime}=\operatorname{Tr}_{AB}\omega$. Then $$E_{\mathrm{sq}}(\omega^{AA\prime:BB\prime})\ge E_{\mathrm{sq}}(\rho^{A:B})+E_{\mathrm{sq}}(\sigma^{A\prime:B\prime}).$$ For every pair of states $\rho^{AB},\sigma^{A\prime B\prime}$, $$E_{\mathrm{sq}}(\rho\otimes\sigma\text{ across }AA\prime:BB\prime)=E_{\mathrm{sq}}(\rho)+E_{\mathrm{sq}}(\sigma).$$ This supplies both general superadditivity and exact product additivity, including unequal factor dimensions.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 3, §II, Proposition 4 (p.1 seed)

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

/-- PDF p.3, Proposition 4 (title/abstract seed on p.1): both superadditivity
and exact tensor-product additivity, for arbitrary unequal local dimensions. -/
theorem superadditivity_and_additivity {A1 B1 : Type} [Fintype A1] [Fintype B1]
    [DecidableEq A1] [DecidableEq B1] [Nonempty A1] [Nonempty B1] :
    (∀ rho : Matrix ((A × A1) × (B × B1)) ((A × A1) × (B × B1)) ℂ,
      IsDensityMatrix rho → sq (firstPair rho) + sq (secondPair rho) ≤ sq rho) ∧
    (∀ (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (A1 × B1) (A1 × B1) ℂ),
      IsDensityMatrix rho → IsDensityMatrix sigma →
      sq (regroupProduct rho sigma) = sq rho + sq sigma) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
