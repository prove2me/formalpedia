-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P16_scalarJumpShift_hamiltonianGauge
-- name    : QAlgorithms.Papers.Independent.Dependency50.P16.scalarJumpShift_hamiltonianGauge
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:50:27.867686+00:00
-- url     : https://prove2.me/theorems/9483309b-a270-4b72-b4c6-e6a91ed91e4b
-- title:
--   Remark C.4: Hamiltonian under scalar jump shifts
-- statement:
--   For a GKSL representation $(H_0,V_k)$, arbitrary scalars $c_k\in\mathbb C$, and $a\in\mathbb R$, set $V'_k=V_k+c_kI$ and
--
--   $$H'_0=H_0+\frac1{2i}\sum_k(\overline{c_k}V_k-c_kV_k^*)+aI.$$
--
--   Then $H'_0$ is Hermitian and $(H'_0,V'_k)$ represents the same GKSL generator. This is the Hamiltonian compensation under scalar jump shifts, with the corrected factor $1/(2i)=-i/2$. The printed factor is $+i/2$; (C.4) forces the opposite sign.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, PDF p. 31, Remark C.4: Hamiltonian under scalar jump shifts

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- arXiv:2308.00561v1, PDF p.31, Remark C.4: Hamiltonian under scalar jump shifts. Correction (traps 23,30): PDF p.31 prints Hnew=H0+(i/2)sum(conj(c_k)Vk-c_k Vk*)+aI. Change only i/2 to 1/(2i)=-i/2; (C.4) and (C.2) force the negative sign for Vnew=V+cI and G=-L. Both Hermiticity and equality of actual generators are retained. -/
theorem scalarJumpShift_hamiltonianGauge {n : ℕ} (hn : 2 ≤ n) (D : LindbladData n)
    (c : Fin D.count → ℂ) (a : ℝ) :
    (shiftedDriftHamiltonian D c a).IsHermitian ∧
      cpGenerator (Complex.I • shiftedDriftHamiltonian D c a + (1 / 2 : ℂ) •
        ∑ k, (gaugeJumps D c k)ᴴ * gaugeJumps D c k) (gaugeJumps D c) = gkslGenerator D := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P16

end
