-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_smTheoremV2_qaoaDense
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.smTheoremV2_qaoaDense
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:43:31.914268+00:00
-- url     : https://prove2.me/theorems/d65d9a1c-6eb7-40a8-87e4-c211740bdd9b
-- title:
--   Supplemental density of generalized QAOA
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
--   $$\overline{G_H}=U(2^n).$$
--
--   The closure is in the usual topology on finite complex matrices. This retains the density strength stated at this supplemental occurrence.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 26, SM Theorem V.2: density of generalized QAOA

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF p.26, SM Theorem V.2 states density, separately from Main Theorem 2's
exact equality. The closure here is explicitly topological, in finite matrices. -/
theorem smTheoremV2_qaoaDense (n : ℕ) (_hn : 1 ≤ n)
    (H : Matrix (Qubits n) (Qubits n) ℂ) (hH : PathConnectedHamiltonian H) :
    closure (generalizedQaoaGroup H : Set (Matrix (Qubits n) (Qubits n) ℂ)) =
      (Matrix.unitaryGroup (Qubits n) ℂ : Set (Matrix (Qubits n) (Qubits n) ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
