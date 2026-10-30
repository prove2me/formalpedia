-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_path_independence
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_path_independence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:08:14.552028+00:00
-- url     : https://prove2.me/theorems/6cbd7886-bef4-449a-b4cb-465a9aea39e2
-- title:
--   Path independence and integrated trace formula for l-body phases
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   Let $T\ge0$ and let an integrable Hermitian invariant Hamiltonian $H(t)$ have an actual unitary propagator $U(t)$ on $[0,T]$, with $U(0)=I$, satisfying the integral Schrödinger equation $U(t)=I+\int_0^t-iH(s)U(s)\,ds$ and integrable $-iHU$. For any integer weights $c(j)$, put $C=\sum_jc(j)\Pi_j$ and $\theta_j=\arg\det(U(T)|_{\mathcal H_j})$. Then, in $\mathbb R/(2\pi\mathbb Z)$,
--   $$\sum_jc(j)\theta_j=-\int_0^T\operatorname{Tr}(H(t)C)\,dt.$$
--   In particular $\Phi_l(U(T))=-\int_0^T\operatorname{Tr}(H(t)C_l)\,dt$ for every even $l$, with zero extension above the physical range. These depend on the endpoint alone. The integral formulation supplies absolute continuity and includes the piecewise continuous controls of finite circuits.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 24, Path independence and integrated trace formula for l-body phases

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P49

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

attribute [local instance 100] LieRing.ofAssociativeRing

-- Specialize the frozen generic aliases without declaring new aliases.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "Vec" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Vec (Qubits n))

-- The frozen support predicate takes the support before the operator.

local notation "WireSupported" => QAlgorithms.Papers.Independent.Information100.P69.Supported

/-- PDF p.24, G2–G5: integrated trace and path independence for an actual
integrable propagator. All equalities of phases take place modulo 2π. -/
theorem phase_path_independence (n : ℕ) (H U : ℝ → Op n) (T : ℝ)
    (hPath : SchrodingerPropagator H U T) :
    (∀ c : Spin n → ℤ, chargePhase (U T) c =
      ((-∫ t in (0 : ℝ)..T, (Matrix.trace (H t * chargeOperator n c)).re : ℝ) : Real.Angle)) ∧
    (∀ l : ℕ, Even l → bodyPhase (U T) l =
      ((-∫ t in (0 : ℝ)..T, (Matrix.trace (H t * central n l)).re : ℝ) : Real.Angle)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
