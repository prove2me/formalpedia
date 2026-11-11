-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_3_6
-- name    : QuantumXoP.Security.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:35.600487+00:00
-- url     : https://prove2.me/theorems/39a4328b-2ac1-4167-9342-1fd1418a0ece
-- title:
--   Theorem 3.6 — exact formula for the advantage against $D_F$
-- statement:
--   Let $D_D$ be any distribution on $F_n$ and $A$ a $q$-query algorithm. Then
--   $$\mathrm{Adv}^{\mathrm{dist}}(D_D,D_F;A)=\big|\langle(\mu_D-1)^{\le2q},P_A\rangle\big|.$$
--
--   Every advantage bound of the paper starts from this identity.
--
--   Differences from the source:
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 12 (PDF p. 14), Theorem 3.6

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 3.6 (p. 12): `Adv^dist(D_D, D_F; A) = |⟨(μ_D − 1)^{≤2q}, P_A⟩|` for every `q`-query
algorithm `A`. -/
theorem theorem_3_6 {n : ℕ} (D : PMF (Fn n)) {q : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Qubits n) (Qubits n) W q) (out : (Qubits n × Qubits n) × W → Bool) :
    adv D (uniformF n) A out = ‖innerF (lowDeg (density D - 1) (2 * q)) (repPoly A out)‖ := by sorry

end QuantumXoP.Security
