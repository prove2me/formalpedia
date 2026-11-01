-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P06_idealEpr_perfectSecretBit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P06.idealEpr_perfectSecretBit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:05:50.774052+00:00
-- url     : https://prove2.me/theorems/4ca58152-eadb-498c-a52a-8eac2b1f5d58
-- title:
--   Measuring an ideal EPR pair yields a perfect secret common bit
-- statement:
--   Let Alice and Bob be qubits, let $E$ be any Hilbert space held by Eve, and let $\omega_{ABE}$ be any normalized positive trace-class density with exact marginal $P_\Phi$, where $\Phi=(|00\rangle+|11\rangle)/\sqrt{2}$. Both parties measure in the displayed $0/1$ basis. Let $\omega_E^{ab}=\langle ab|\omega|ab\rangle$ be the unnormalized Eve block for outcomes $a,b$, and let $\tau_E=\operatorname{Tr}_{AB}\omega$. Then $\tau_E$ is normalized and
--
--   $$
--   \omega_E^{ab}=\begin{cases}\tfrac12\tau_E,&a=b,\\0,&a\ne b.\end{cases}
--   $$
--
--   Consequently the outcomes $00$ and $11$ each have probability $1/2$, the outcomes $01$ and $10$ have probability zero, and the common bit is exactly independent of Eve. Eve need not purify $\omega$, and her Hilbert dimension is unrestricted.
--
--   The operator identity captures perfect secrecy against every Eve measurement. It concerns a single ideal pair; it does not assert a noisy-protocol security theorem or a key rate.
-- source:
--   Is Entanglement Monogamous?, arXiv:quant-ph/0307120v1, PDF p. 6, Section II, unnumbered: measuring an ideal EPR pair gives a perfect secret common bit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

open QAlgorithms.Papers.Independent.Frontier18.P09 (partialTraceRightCoeff)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section II, arXiv:quant-ph/0307120v1, PDF p.6, using the exact state
(1) on p.5: both basis measurements give the same uniform bit independent of
Eve. The full unnormalized operator blocks encode secrecy against every Eve
measurement, in arbitrary Hilbert dimension, even when omega is mixed.
No noisy-protocol or asymptotic key-rate claim is made. -/
theorem idealEpr_perfectSecretBit {E : Type}
    (omega : Matrix ((Opinion × Opinion) × E) ((Opinion × Opinion) × E) ℂ)
    (hstate : IsCoordinateDensity omega) (hepr : partialTraceRightCoeff omega = eprDensity) :
    IsCoordinateDensity (traceLeft omega) ∧
      ∀ a b : Opinion, eveBlock omega a b =
        if a = b then (1 / 2 : ℂ) • traceLeft omega else 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P06

end
