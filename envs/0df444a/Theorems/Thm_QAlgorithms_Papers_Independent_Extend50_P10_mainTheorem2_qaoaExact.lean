-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_mainTheorem2_qaoaExact
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.mainTheorem2_qaoaExact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:37:16.366993+00:00
-- url     : https://prove2.me/theorems/d24ce462-c09d-4496-b5fb-31f94397e5c8
-- title:
--   Generalized QAOA generates the full unitary group
-- statement:
--   Let $n\ge1$ and let $H$ be a fixed Hermitian Hamiltonian whose off-diagonal index graph in the $n$-qubit computational basis is connected. Set $Z_0=I$ and let $Z_i$ act as Pauli $Z$ on site $i$ for $1\le i\le n$. Let $G_H$ consist of all finite products of mixer evolutions $e^{-itH}$, $t\in\mathbb R$, and diagonal evolutions $e^{-iH_Z(\beta)}$, where
--
--   $$
--   H_Z(\beta)=\sum_{k,l=0}^n\beta_{kl}Z_kZ_l,\qquad \beta_{kl}\in\mathbb R.
--   $$
--
--   The coefficients vary independently at every use, and the mixer $H$ stays fixed.
--
--   Then
--
--   $$G_H=U(2^n).$$
--
--   This is exact finite-product universality, with no bound on the required word length.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 7, Main Theorem 2: generalized QAOA universality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.7, Main Theorem 2: exact finite-product equality with the full unitary
group. The identity, all single Zs and all two-site ZZs are available. -/
theorem mainTheorem2_qaoaExact (n : ℕ) (_hn : 1 ≤ n)
    (H : Matrix (Qubits n) (Qubits n) ℂ) (hH : PathConnectedHamiltonian H) :
    (generalizedQaoaGroup H : Set (Matrix (Qubits n) (Qubits n) ℂ)) =
      (Matrix.unitaryGroup (Qubits n) ℂ : Set (Matrix (Qubits n) (Qubits n) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
