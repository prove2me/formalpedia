-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_fixed_purification_channels
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.fixed_purification_channels
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:35:17.526979+00:00
-- url     : https://prove2.me/theorems/8ddafef4-ba18-4d0c-a690-c6b6f2f0772d
-- title:
--   Fixed-purification channel characterization
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Fix a unit purification $\Psi^{ABC}$ of a state $\rho^{AB}$. For each positive finite output dimension, a matrix $\omega^{ABE}$ is an extension of $\rho$ if and only if there exists a CPTP channel $\Lambda:C\to E$ with $\omega=(\mathrm{id}_{AB}\otimes\Lambda)(|\Psi\rangle\langle\Psi|)$. Moreover, $$E_{\mathrm{sq}}(\rho)=\inf_{\substack{E\text{ finite}\\\Lambda:C\to E\text{ CPTP}}}\frac12 I(A;B|E)_{(\mathrm{id}\otimes\Lambda)(|\Psi\rangle\langle\Psi|)}.$$ This replaces the search over extensions by channels acting on one fixed purification.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 5, §III, equation (3)

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

/-- PDF p.5, equation (3): every physical extension is a CPTP image of ONE
fixed purification, and the channel-infimum gives the same unrestricted value.
The choice of channel follows the extension; output dimensions have no cap. -/
theorem fixed_purification_channels {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hpsi : ‖psi‖ = 1)
    (hpur : traceRight (pureDensity psi) = rho) :
    (∀ e : ℕ, 0 < e →
      ∀ omega : Matrix ((A × B) × Fin e) ((A × B) × Fin e) ℂ,
        (IsDensityMatrix omega ∧ traceRight omega = rho) ↔
        ∃ L : Superop C (Fin e), IsChannel L ∧
          omega = idTensorSuperop L (pureDensity psi)) ∧
    sq rho = sInf {x : ℝ | ∃ e : ℕ, 0 < e ∧ ∃ L : Superop C (Fin e),
      IsChannel L ∧ x = cmi (idTensorSuperop L (pureDensity psi)) / 2} := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
