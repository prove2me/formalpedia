-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_publicInstruments_average_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.publicInstruments_average_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:16:42.519043+00:00
-- url     : https://prove2.me/theorems/b7242857-df08-49bb-986e-1739f0f90487
-- title:
--   Remark II.6: average monotonicity under public local instruments
-- statement:
--   Let $\rho_{AB}$ be a density matrix on arbitrary finite nonzero complex spaces. Consider any finite adaptive protocol in which, at each node, either Alice or Bob applies a finite rectangular quantum instrument and publicly announces its outcome. Arbitrary finite local dimensions, private Kraus multiplicities, and choices depending on earlier messages are allowed. Write $p_t$ for the probability of a full transcript $t$ and $\rho_t$ for its normalized final state when $p_t>0$. Then
--
--   $$\sum_{t:p_t>0}p_t I(A_t:B_t)_{\rho_t}\le I(A:B)_\rho.$$
--
--   For one instrument this is $\sum_{i:p_i>0}p_iI(A':B)_{\rho_i}\le I(A:B)_\rho$, with the analogous statement when Bob acts. Zero branches contribute zero without normalization. Thus the theorem retains both the one-step inequality and its finite iteration, counting correlations conditional on the public transcript.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 5, Remark II.6: average monotonicity under public local instruments

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P47

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies localProduct)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation first)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon Config)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5--6, Remark II.6: public local instruments decrease total correlation on
average, including every finite iteration. A one-node tree is the inequality (13). -/
theorem publicInstruments_average_monotonicity (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hrho : IsDensityMatrix rho)
    (P : PublicProtocol a b) : P.average rho ≤ mutualInformation rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
