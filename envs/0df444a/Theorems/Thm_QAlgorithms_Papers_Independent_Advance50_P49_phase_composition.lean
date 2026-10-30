-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_phase_composition
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.phase_composition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:10:53.8426+00:00
-- url     : https://prove2.me/theorems/d29eb464-349e-4512-a01e-58bc8321946e
-- title:
--   l-body phases are group homomorphisms
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For every even $l\ge0$ and invariant unitaries $V,W$,
--   $$\Phi_l(WV)=\Phi_l(W)+\Phi_l(V)\pmod{2\pi},\qquad \Phi_l(I)=0.$$
--   For $l>2\lfloor n/2\rfloor$, the phase is identically zero. This is the additive-angle form of the group-character statement, including $l=0$.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 25, l-body phases are group homomorphisms

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

/-- PDF p.25, G12: every even-body phase, including l=0, is a group character. -/
theorem phase_composition (n l : ℕ) (hl : Even l) :
    bodyPhase (1 : Op n) l = 0 ∧
    (∀ V W : Op n, SymUnitary V → SymUnitary W →
      bodyPhase (W*V) l = bodyPhase W l + bodyPhase V l) ∧
    (2*(n/2)<l → ∀ V : Op n, bodyPhase V l=0) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
