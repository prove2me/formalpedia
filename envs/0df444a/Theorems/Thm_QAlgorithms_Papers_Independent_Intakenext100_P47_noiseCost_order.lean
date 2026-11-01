-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P47_noiseCost_order
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P47.noiseCost_order
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:11:16.101791+00:00
-- url     : https://prove2.me/theorems/6390743e-08a3-44bf-8821-c98a7531864b
-- title:
--   Section II, Eq. (4): ordering of three finite noise costs
-- statement:
--   Let $\rho_{AB}$ be a density matrix on finite nonzero complex spaces, and let $R(\tau)=\sum_{i=1}^N p_i(U_i\otimes V_i)\tau(U_i\otimes V_i)^\dagger$ be a chosen finite product-unitary ensemble, with $N\ge1$, $p_i\ge0$, and $\sum_i p_i=1$. Let $H(p)=-\sum_i p_i\log_2p_i$, using $0\log_20=0$. If $\psi$ purifies $\rho$, define $S_e(R,\rho)=S((\mathrm{id}\otimes R)(\psi))$. Then
--
--   $$\log_2N\ge H(p)\ge S_e(R,\rho).$$
--
--   The first two costs depend on the implementing ensemble, whereas the last depends only on its channel and the source state. This orders the finite noise resources used in the erasure converses.
-- source:
--   On the quantum, classical and total amount of correlations in a quantum state, arXiv:quant-ph/0410091v2, PDF p. 3, Section II, Eq. (4): ordering of three finite noise costs

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

/-- PDF p.3, (4): the three costs of a chosen implementing ensemble are ordered. -/
theorem noiseCost_order {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : Matrix (A × B) (A × B) ℂ)
    (hrho : IsDensityMatrix rho) (R : COLUR A B) :
    entropyExchange R.operation rho ≤ shannon R.weight ∧
    shannon R.weight ≤ Real.logb 2 R.count := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P47

end
