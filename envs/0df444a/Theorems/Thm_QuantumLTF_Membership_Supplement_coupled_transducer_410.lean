-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_coupled_transducer_410
-- name    : QuantumLTF.Membership.Supplement.coupled_transducer_410
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-24T06:02:14.043523+00:00
-- url     : https://prove2.me/theorems/18ac2e42-e3f5-49c8-b693-d46d8a018017
-- title:
--   Coupled Transducer Correctness and Catalyst Energy Bound for Bounded-Size Majority
-- statement:
--   This theorem establishes the algebraic correctness, unitarity, parity-lift invariants, and logarithmic catalyst-energy bound for the coupled transducer construction of Krivcenko, Nguyen, and de Wolf (2026) under the bounded-size promise $1 \le |A| \le k$.
--
--   Specifically, using the definitions in `QuantumLTF_Membership_Supplement_coupledOp410`:
--
--   1. **Block unitarity:** For every cutoff $M \ge 0$, Hamming weight $t \ge 0$, and interior index $j \ge 0$, the step operator $U_t$ (`U_op410 M t`) and the $2 \times 2$ plane rotations `R2J j` and `R2Top M` are unitary.
--   2. **Odd-cardinality parity lift:** For every $A \subseteq [n]$ with $1 \le |A| \le k$, `liftOdd A` agrees with $A$ on `[n]`, has odd cardinality $2m+1$ with $m = \operatorname{layerOf}(A) \le \lfloor k/2 \rfloor$, and satisfies $\operatorname{maj}_{\operatorname{liftOdd}(A)}(x, 1) = \operatorname{maj}_A(x)$ and $\operatorname{maj}_{\operatorname{liftOdd}(A)}(\bar{x}, 0) = -\operatorname{maj}_A(x)$ for every $x \in \{\pm 1\}^n$ (Equation (127)).
--   3. **Logarithmic catalyst norm bound:** There exists an absolute constant $C_0 > 0$ such that for all $2 \le k \le n$ and $A$ with $1 \le |A| \le k$, the catalyst state $|w_A\rangle$ (`wCatVec410`) is supported strictly on the private space $W$ (`modeKet M 0` amplitude is $0$) and satisfies
--   $$
--   \| |w_A\rangle \|^2 \le C_0 \ln k.
--   $$
--   4. **Phase-query and transducer step relations:** Letting $B = \operatorname{liftOdd}(A)$ of odd size $2m+1 \le n'$ with $1 \le m \le M$ with $0 \le m \le M$ and $M \ge 1$, the controlled Majority phase query $I_{\mathbb{C}} \oplus O_B^{\pm}$ (`phaseCtrl410`) maps $|w_B\rangle$ to $|w'_B\rangle$ (`wCatAfter410`), and the ideal transducer unitary $U_{\mathrm{ideal}} = \hat{H} \tilde{U} \hat{H}$ (`U_ideal410`) satisfies
--   $$
--   U_{\mathrm{ideal}}\bigl(|V\rangle|0^{n'}\rangle + |w'_B\rangle\bigr) = |V\rangle|\mathbf{1}_B\rangle + |w_B\rangle.
--   $$
--
--   This isolates the polynomial-method and two-level-rotation algebra needed for Theorem 4.10 into a self-contained algebraic interface between the adversary SDP dual and the gate-level clocked quantum walk.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Section 4.3, Lemma 4.5, Eq. (118)-(127) (pp. 45-50), Section 4.5.3, Eq. (144)-(148) (pp. 55-57), and Appendix C.5.2 (pp. 96-99).

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Majority CoupledOp410

theorem coupled_transducer_410 :
    (∀ M t, U_op410 M t ∈ Matrix.unitaryGroup (Qubits (qW M)) ℂ) ∧
    (∀ j, R2J j ∈ Matrix.unitaryGroup Bool ℂ) ∧
    (∀ M, R2Top M ∈ Matrix.unitaryGroup Bool ℂ) ∧
    (∀ {n k : ℕ} (A : BoundedSupports n k),
      (∀ i : Fin n, i.castSucc ∈ liftOdd A ↔ i ∈ A.1) ∧
      ((liftOdd A).card = 2 * layerOf A + 1 ∧ layerOf A ≤ k / 2) ∧
      (∀ x : Qubits n, majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) x true) = majorityBit A.1 x) ∧
      (∀ x : Qubits n, majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) (fun i => !(x i)) false) = !(majorityBit A.1 x))) ∧
    (∀ {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) (S : Qubits n'),
      wCatVec410 n' M m B hB (modeKet M 0, S) = 0) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k n : ℕ), 2 ≤ k → k ≤ n →
      ∀ (A : BoundedSupports n k) (hB : (liftOdd A).card = 2 * layerOf A + 1),
        ‖wCatVec410 (n + 1) (k / 2) (layerOf A) (liftOdd A) hB‖ ^ 2 ≤ C₀ * Real.log k) ∧
    (∀ {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1),
      act (phaseCtrl410 M n' B) (wCatVec410 n' M m B hB) = wCatAfter410 n' M m B hB) ∧
    (∀ {n' M m : ℕ} (_hM : 1 ≤ M) (_hmM : m ≤ M) (_hle : 2 * m + 1 ≤ n')
      (B : Finset (Fin n')) (hB : B.card = 2 * m + 1),
      act (U_ideal410 M n') (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB) =
        tensorVec (ket (modeKet M 0)) (ket (fun i : Fin n' => decide (i ∈ B))) + wCatVec410 n' M m B hB) := by
  sorry

end QuantumLTF.Membership.Supplement
