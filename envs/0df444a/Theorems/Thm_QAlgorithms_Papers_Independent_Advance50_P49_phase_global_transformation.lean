-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_global_transformation
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_global_transformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:09:16.691998+00:00
-- url     : https://prove2.me/theorems/20cb1f0e-1f77-4a95-b035-8fa2e8c6f0f2
-- title:
--   Global-phase transformation law and observability
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For invariant unitary $V$, define $\Phi_l(V)=\sum_jc_l(j)\arg\det(V|_{\mathcal H_j})$ modulo $2\pi$. For every real $\alpha$ and every even $l\ge0$,
--   $$\Phi_l(e^{i\alpha}V)=\Phi_l(V)+2^n\alpha\,\delta_{l0}\pmod{2\pi},\qquad \Phi_0(V)=\arg\det V.$$
--   Consequently every positive even-body phase is unchanged by global phase and defines a physical projective-unitary invariant. The paper's observability claim is exactly this invariance; no experimental resource bound is asserted.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 24, Global-phase transformation law and observability

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

/-- PDF pp.4,24, G6: global-phase transformation, including Φ_0=arg det V.
Positive-body phases therefore descend to physical global-phase classes. -/
theorem phase_global_transformation (n : ℕ) (V : Op n) (hV : SymUnitary V) :
    bodyPhase V 0 = ((Complex.arg (Matrix.det V) : ℝ) : Real.Angle) ∧
    ∀ (l : ℕ) (alpha : ℝ), Even l →
      bodyPhase (Complex.exp (Complex.I*alpha) • V) l = bodyPhase V l +
        if l=0 then ((2^n : ℕ) • (alpha : Real.Angle)) else 0 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
