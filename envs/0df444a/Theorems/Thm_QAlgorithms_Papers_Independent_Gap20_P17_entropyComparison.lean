-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_entropyComparison
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.entropyComparison
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:38:03.88032+00:00
-- url     : https://prove2.me/theorems/3e3a8dfb-e821-41d4-bada-10079fb118c3
-- title:
--   Entropy identity and entropy-increasing channel comparison
-- statement:
--   All registers are finite. A physical channel is completely positive and trace preserving; its fixed Stinespring isometry $V:A\to B\otimes E$ defines the receiver channel $\Lambda$ and its complementary channel $\Lambda^c$. Inputs $\rho$ are positive semidefinite of trace one. Entropies are in bits. Write $I(\Lambda,\rho)=S(\Lambda(\rho))-S(\Lambda^c(\rho))$ and $I_R(\Lambda,\rho)=S(\rho)-S(\Lambda^c(\rho))$. These equal the purified-reference definitions, with the reference retained by Alice.
--
--   Operational capacities are supremal asymptotic ebits per physical channel use, with vanishing full-state trace-norm error, arbitrary finite block memories, and no initial shared entanglement. $E$ allows local processing without classical assistance; $E_{\leftarrow}$ permits adaptive feedback; $E_{\leftrightarrow}$ permits both classical directions. $E_{\triangleleft}$ sends the entire block before one final Bob-to-Alice message and Alice's conditional operation. Rate zero is included. For every input,
--
--   $$I_R(\Lambda,\rho)-I(\Lambda,\rho)=S(\rho)-S(\Lambda(\rho)).$$
--
--   If $S(\Lambda(\sigma))\ge S(\sigma)$ for every density input $\sigma$, and $I_1=\max_\sigma I(\Lambda,\sigma)$, $R_1=\max_\sigma I_R(\Lambda,\sigma)$, then
--
--   $$E(\Lambda)\ge I_1(\Lambda)\ge R_1(\Lambda).$$
--
--   The all-input entropy premise fixes the comparison direction. Only the finite-register statement is asserted.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 3, paragraph following Eq.(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: the pointwise entropy-difference identity, and the capacity ordering
under the stated all-input entropy-increase hypothesis. No optical extension. -/
theorem entropyComparison {a b e : ℕ} (ha : 0 < a)
    (V : Matrix (Fin b × Fin e) (Fin a) ℂ) (hV : IsIsometry V)
    (rho : Matrix (Fin a) (Fin a) ℂ) (hrho : IsDensityMatrix rho) :
    reverseInfo V rho - forwardInfo V rho =
      vnEntropy rho - vnEntropy (receiverChannel V rho) ∧
    ((∀ sigma : Matrix (Fin a) (Fin a) ℂ, IsDensityMatrix sigma →
      vnEntropy sigma ≤ vnEntropy (receiverChannel V sigma)) →
      (forwardMaximum V : EReal) ≤ entanglementCapacity (receiverChannel V) .unassisted ∧
      reverseMaximum V ≤ forwardMaximum V) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
