-- Prove2me | Theorems.Thm_QuantumXoP_Security_claim_3_7
-- name    : QuantumXoP.Security.claim_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:25.172257+00:00
-- url     : https://prove2.me/theorems/ab4e1b19-0915-40fb-bee5-a7aa0619d9f6
-- title:
--   Claim 3.7 — the amplitudes of a $q$-query algorithm have Fourier degree at most $q$
-- statement:
--   Let $A$ be a $q$-query algorithm with oracle $O_f$, $f\in F_n$, and write its final state before the measurement as $\sum_z p^{(q)}_z(f)\,|z\rangle$. Then for every basis state $z$ the amplitude
--   $$f\mapsto p^{(q)}_z(f)$$
--   is a functional of Fourier degree at most $q$.
--
--   It is the inductive step behind Theorem 3.4.
--
--   Differences from the source:
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 13 (PDF p. 15), Claim 3.7 (inside the proof of Theorem 3.4)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Claim 3.7 (p. 13): every amplitude `p_z^{(q)}(f) = ⟨z|ψ_q^f⟩` of the final state (before the
measurement) of a `q`-query algorithm is a functional of Fourier degree at most `q`. -/
theorem claim_3_7 {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits n) (Qubits n) W q) (z : (Qubits n × Qubits n) × W) :
    FourierDegLE (fun f : Fn n => A.finalState (xorOracle f) z) q := by sorry

end QuantumXoP.Security
