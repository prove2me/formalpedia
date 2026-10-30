-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P49_six_wire_commutator
-- name    : QAlgorithms.Papers.Independent.Advance50.P49.six_wire_commutator
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:18:29.698475+00:00
-- url     : https://prove2.me/theorems/33da6fa5-08f7-404b-804b-4029f5d6d5d8
-- title:
--   Explicit six-qubit commutator identity
-- statement:
--   Use the physical register $\mathcal H_n=(\mathbb C^2)^{\otimes n}$. Rotational invariance means commuting with $U^{\otimes n}$ for every one-qubit unitary $U$. The legal spins are $j=n/2-r$, $r=0,\ldots,\lfloor n/2\rfloor$, and $\Pi_j$ is the actual spectral projector of $J^2$ at $j(j+1)$. Write $R_{ab}=(X_aX_b+Y_aY_b+Z_aZ_b)/2$ and $\mathcal V_k,\mathfrak v_k$ for the group of finite compositions of $k$-local invariant gates and its generated real Lie algebra, including scalar phases. Exchange-only circuits contain finite products of $e^{-itR_{ab}}$ with real $t$. Set $C_0=I$ and, for even $l>0$, $C_l=(l/2)!^{-1}\sum_{i_1,\ldots,i_l\ \mathrm{distinct}}R_{i_1i_2}\cdots R_{i_{l-1}i_l}$. Extend $C_l=0$ above $2\lfloor n/2\rfloor$. Its sector eigenvalue is $c_l(j)=\operatorname{Tr}(C_l\Pi_j)/\operatorname{Tr}(\Pi_j)$. All body-index sums below are over even indices.
--
--   For any six distinct physical wires, let $[A,B]=AB-BA$. Then
--   $$4(R_{12}R_{34}-R_{34}R_{56})=-[[[[R_{12},R_{23}],R_{34}],R_{45}],R_{51}]-[[[[R_{23},R_{34}],R_{45}],R_{56}],R_{62}]-[[R_{13},R_{23}],R_{24}]+[[R_{35},R_{45}],R_{46}].$$
--   All brackets are left nested. Dividing the right side by four and preparing wires 5,6 in $|00\rangle$ gives the action of $R_{12}R_{34}-R_{34}/2$ on every four-qubit vector. Also $S=I/4+(R_{12}+R_{34})/2+R_{12}R_{34}$. These identities supply the explicit base construction up to the swap's scalar shift.
-- source:
--   Rotationally-Invariant Circuits: Universality with the exchange interaction and two ancilla qubits, arXiv:2202.01963v1, PDF p. 34, Explicit six-qubit commutator identity

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

/-- PDF pp.5,34, I32: exact left-nested six-wire identity, and the corresponding
four-qubit action when wires 5,6 are prepared in |00⟩. -/
theorem six_wire_commutator (n : ℕ) (w : Fin 6 ↪ Fin n) :
    (4 : ℂ) • (heisenbergExchange (w 0) (w 1)*heisenbergExchange (w 2) (w 3) -
      heisenbergExchange (w 2) (w 3)*heisenbergExchange (w 4) (w 5)) =
      commutatorTemplate w (templateSeeds w) ∧
    multiSwap 2 = (1/4 : ℂ) • (1 : Op 4) +
      (1/2 : ℂ) • (heisenbergExchange (0 : Fin 4) 1+heisenbergExchange (2 : Fin 4) 3) + standardQ 4 4 ∧
    (∀ psi : Vec 4,
      act ((1/4 : ℂ) • commutatorTemplate (Function.Embedding.refl (Fin 6))
        (templateSeeds (Function.Embedding.refl (Fin 6)))) (tensorState psi (zeroKet 2)) =
        tensorState (act (standardQ 4 4-(1/2 : ℂ) • heisenbergExchange (2 : Fin 4) 3) psi) (zeroKet 2)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P49

end
