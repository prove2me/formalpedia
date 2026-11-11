-- Prove2me | Theorems.Thm_UnitaryQIPPSPACE_theorem_3_1
-- name    : UnitaryQIPPSPACE.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:13.456022+00:00
-- url     : https://prove2.me/theorems/24d28d04-29df-4f30-83fc-b228ba37b81a
-- title:
--   Theorem 3.1 — a near-optimal prover in polynomial space [MY23]
-- statement:
--   Let $\{V_n\}$ be a time-uniform family of well-formed quantum verifiers that receive no input state, and let $\omega^*_n$ be the supremum, over all provers, of the probability that $V_n$ accepts. Then for every polynomial $q$ there are a space-uniform family of unitary circuits $\{P_n\}$, $P_n$ acting on the message register of $V_n$ followed by $y(n)$ private qubits, such that the prover $P_n$ makes $V_n$ accept with probability at least
--   $$\omega^*_n-\frac1{q(n)+1}.$$
--
--   This is how the proof of Theorem 1.1 replaces the honest prover by a polynomial-space algorithm.
--
--   Differences from the source:
--   - reading: ω*_n is "the maximum acceptance probability of V_n over all provers" → ω*_n is the supremum of the acceptance probabilities over all provers; reason: the values lie in [0,1]; the supremum is the maximum whenever one exists
--   - encoding: for every polynomial q, error 1/q(n) → for every q ∈ ℕ[X], error 1/(q(n)+1); reason: over all such q this is equivalent to all real polynomials q ≥ 1
--   - encoding: the gate set G is fixed "without loss of generality, … for example, {H, T, CNOT}" → G = {H, T, CNOT} exactly; reason: the paper's own example; the classes do not depend on the choice of a finite universal gate set
--   - encoding: deterministic Turing machines → the published oracle Turing machines QAdvFew.PoQOracle.OTM run with the empty oracle; descriptions are tuple codes; reason: a standard machine model and a fixed injective code; polynomial time and space are preserved
--   - reading: space-uniform: a polynomial-space machine "on input (1^n, i), outputs the i-th operation of C_n" → for every i ≤ |C_n| the machine on (1^n, bin i) uses at most p(n) cells and outputs the i-th operation, or the empty string at i = |C_n|; reason: the end marker makes the machine determine the circuit (the standard reading of [MY23]); it bounds |C_n| by 2^{O(p(n))}
--   - encoding: a prover is a unitary on (M, Y) with an arbitrarily large private register Y → any number y of private qubits and any unitary on M ⊗ Y, private register starting in |0⋯0⟩; reason: the paper's model, with y chosen by the prover
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Theorem 3.1 ([MY23, Theorem 7.1], reformulated), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_run
import Definitions.Def_UnitaryQIPPSPACE_TimeUniformVerifiers
import Definitions.Def_UnitaryQIPPSPACE_SpaceUniform

namespace UnitaryQIPPSPACE

/-- **Theorem 3.1** ([MY23, Theorem 7.1], reformulated; He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, p. 13 (PDF p. 15)): "Let `{V_n}` be a time-uniform
family of quantum verifiers that receive no input state. Let `ω*_n` be the maximum acceptance
probability of `V_n` over all provers that interact with `V_n`. Then, for every polynomial `q(n)`,
there exists a space-uniform family of unitary circuits `{P_n}` such that the prover `P_n` makes
`V_n` accept with probability at least `ω*_n − 1/q(n)`."

"Receive no input state": the input has `0` qubits (`Z_work` starts in `|0⋯0⟩`). `ω*_n` is the
supremum of the acceptance probability over all provers (any private register size, any unitary,
private register starting in `|0⋯0⟩`). `P_n` is a unitary circuit on `m_n + y(n)` qubits (the
message register `M` of `V_n`, then `y(n)` private qubits), space uniform with `m_n + y(n)` input
qubits; as a prover it acts by its unitary.

**Formalization Note** `1/q(n)` is written `1/(q(n) + 1)` with `q` a polynomial with
natural-number coefficients; ranging over all such `q` this is equivalent to all real polynomials
`q ≥ 1`. The supremum is taken over a nonempty set of numbers in `[0, 1]`. -/
theorem theorem_3_1 (V : ℕ → Verifier) (hWF : ∀ n, (V n).WF) (hV : TimeUniformVerifiers V)
    (q : Polynomial ℕ) :
    ∃ (Pc : ℕ → Circuit) (y : ℕ → ℕ), SpaceUniform Pc (fun n => (V n).m + y n) ∧
      ∀ n, (Pc n).IsUnitary ∧ (Pc n).WF ((V n).m + y n) ((V n).m + y n) ∧
        sSup {r : ℝ | ∃ P : Prover (V n).m,
            r = acceptProb (V n) (P.U : Matrix _ _ ℂ) 0 (fun _ => 1) (zeroState P.y)}
          - 1 / (((q.eval n : ℕ) : ℝ) + 1)
          ≤ acceptProb (V n) (circuitProver (Pc n) (V n).m (y n)) 0 (fun _ => 1) (zeroState (y n)) := by sorry

end UnitaryQIPPSPACE
