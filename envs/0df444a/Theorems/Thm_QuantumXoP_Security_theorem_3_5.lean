-- Prove2me | Theorems.Thm_QuantumXoP_Security_theorem_3_5
-- name    : QuantumXoP.Security.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:38.784596+00:00
-- url     : https://prove2.me/theorems/ec15eb2b-f0d6-4714-9e27-75e9e16516ff
-- title:
--   Theorem 3.5 — the advantage is an inner product with $(\mu_D-1)^{\le 2q}$
-- statement:
--   Let $D_D$ be a distribution on $F_n$ with density $\mu_D(f)=\Pr[f\leftarrow D_D]/(1/|F|)$, and let $A$ be a binary-output algorithm making at most $q$ queries, with representing polynomial $P_A$. Then
--   $$\Pr_{f\leftarrow D_D}[A^{O_f}\to1]-\Pr_{f\leftarrow F}[A^{O_f}\to1]=\langle\mu_D-1,P_A\rangle=\langle(\mu_D-1)^{\le2q},P_A\rangle .$$
--
--   Only the Fourier coefficients of $\mu_D$ of degree at most $2q$ affect a $q$-query distinguisher.
--
--   Differences from the source:
--   - encoding: a quantum oracle algorithm ends with a binary measurement (Π₀, Π₁ = I − Π₀) of its final state → the published QueryAlg is measured in the computational basis and an arbitrary output map out : (query register × workspace) → Bool gives the output bit; the workspace W and the final unitary U_q are arbitrary; reason: same class of algorithms: every binary projective measurement is a unitary followed by a computational-basis measurement
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 12 (PDF p. 14), Theorem 3.5

import Mathlib
import Definitions.Def_QuantumXoP_Security_Advantage

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Theorem 3.5 (p. 12): for an algorithm making at most `q` queries,
`Pr_{f←D_D}[A^{O_f} → 1] − Pr_{f←F}[A^{O_f} → 1] = ⟨μ_D − 1, P_A⟩ = ⟨(μ_D − 1)^{≤2q}, P_A⟩`. -/
theorem theorem_3_5 {n : ℕ} (D : PMF (Fn n)) {q q' : ℕ} (hq : q' ≤ q)
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : QueryAlg (Qubits n) (Qubits n) W q') (out : (Qubits n × Qubits n) × W → Bool) :
    (((accProb D A out - accProb (uniformF n) A out : ℝ)) : ℂ) =
        innerF (density D - 1) (repPoly A out) ∧
      innerF (density D - 1) (repPoly A out) =
        innerF (lowDeg (density D - 1) (2 * q)) (repPoly A out) := by sorry

end QuantumXoP.Security
