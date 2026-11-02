-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P66_unbiasedChoiSnapshots
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P66.unbiasedChoiSnapshots
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:48:47.260058+00:00
-- url     : https://prove2.me/theorems/c9bc0861-650b-4930-9029-0c0676c6708b
-- title:
--   Unbiased full Choi snapshots
-- statement:
--   Let $\mathcal E$ be any CPTP map on $n\ge1$ qubits with normalized reference-first Choi state $\rho_{\Lambda}=2^{-n}\Lambda_{\mathcal E}$. Fix an ideal Pauli-6, global Clifford, or fixed block-factorized measurement frame independently of $\mathcal E$. Draw a fresh uniform basis $U$ and its computational Born outcome $b$ on $\rho_{\Lambda}$. Using the actual linear inverse measurement channel, form
--
--   $$
--   \widehat\Lambda=2^n\mathcal M^{-1}(U^\dagger|b\rangle\langle b|U).
--   $$
--
--   Then
--
--   $$
--   \mathbb E[\widehat\Lambda]=\Lambda_{\mathcal E}.
--   $$
--
--   The global inverse acts in dimension $2^{2n}$, while the external factor is $2^n$. Individual snapshots may be indefinite and need not be CPTP or pure. This unbiased representation underlies linear prediction; no preservation of expectation by nonlinear postprocessing is asserted.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, PDF p. 2, Section II; Eq.(7) on PDF p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Section II, PDF p.2, Eq.(7), PDF p.4: one unbiased unnormalized Choi
snapshot for any CPTP process. A snapshot need not be positive, pure or CPTP. -/
theorem unbiasedChoiSnapshots (n : ℕ) (hn : 0 < n) (F : BasisChoiceFrame (n + n))
    (hF : PaperFrame F) (E : Superop (Qubits n) (Qubits n)) (hE : IsChannel E) :
    meanChoiSnapshot F E = processChoi E := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P66

end
