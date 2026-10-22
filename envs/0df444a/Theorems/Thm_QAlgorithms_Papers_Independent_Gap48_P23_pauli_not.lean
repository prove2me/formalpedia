-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_pauli_not
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.pauli_not
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:06:19.384784+00:00
-- url     : https://prove2.me/theorems/f61cf556-56c6-4261-91d3-c6cbc260329a
-- title:
--   Example E.2: random Pauli implementation of UNOT
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   For every single-qubit operator $\rho$, the one-input physical UNOT channel is
--   $$\Phi_{\rm UNOT}^1(\rho)=\frac13(X\rho X^\dagger+Y\rho Y^\dagger+Z\rho Z^\dagger),$$
--   where $X,Y,Z$ are the Pauli matrices. Thus applying one of these three matrices with equal probability implements this channel.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 74, Example E.2: random Pauli implementation of UNOT

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.74, Example E.2: random Pauli implementation, with probabilities 1/3. -/
theorem pauli_not (rho : Op (Fin 2)) :
    universalNotChannel 1 rho = (1/3 : ℂ) •
      (conjSuperop (!![0,1;1,0] : Op (Fin 2)) rho +
       conjSuperop (!![0,-Complex.I;Complex.I,0] : Op (Fin 2)) rho +
       conjSuperop (!![1,0;0,-1] : Op (Fin 2)) rho) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
