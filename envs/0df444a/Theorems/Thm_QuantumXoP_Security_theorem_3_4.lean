-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_3_4
-- name    : QuantumXoP.Security.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:28.141785+00:00
-- url     : https://prove2.me/theorems/cb7b0a55-bf13-4bcf-b63f-ad56d982588b
-- title:
--   Theorem 3.4 — the acceptance probability has Fourier degree at most $2q$ and norm at most 1
-- statement:
--   Let $A$ be a quantum algorithm making $q$ queries to $O_f$, $f\in F_n$, and outputting a bit. The functional $P_A(f)=\Pr[A^{O_f}\to1]$ has Fourier degree at most $2q$:
--   $$\Pr[A^{O_f}\to1]=P_A(f)=\sum_{|\gamma|\le2q}\widehat P_A(\gamma)\,\chi_\gamma(f),$$
--   and $\|P_A\|_2\le1$.
--
--   $P_A$, the representing polynomial of $A$, is the bridge between algorithms and Fourier analysis used in every later bound.
--
--   Differences from the source:
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), pp. 11–12 (PDF pp. 13–14), Theorem 3.4

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 3.4 (pp. 11–12): the acceptance probability `P_A(f) = Pr[A^{O_f} → 1]` of a `q`-query
algorithm is a functional of Fourier degree at most `2q`, and `‖P_A‖₂ ≤ 1`. -/
theorem theorem_3_4 {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits n) (Qubits n) W q) (out : (Qubits n × Qubits n) × W → Bool) :
    FourierDegLE (repPoly A out) (2 * q) ∧ l2norm (repPoly A out) ≤ 1 := by sorry

end QuantumXoP.Security
