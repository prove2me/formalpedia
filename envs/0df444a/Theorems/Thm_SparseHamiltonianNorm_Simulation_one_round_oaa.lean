-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_one_round_oaa
-- name    : SparseHamiltonianNorm.Simulation.one_round_oaa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:35.698127+00:00
-- url     : https://prove2.me/theorems/b6c75c26-135b-47c0-a61b-abcdead1b64a
-- title:
--   Lemma 5 — One-round robust oblivious amplitude amplification
-- statement:
--   Let a supplied finite circuit $A_0$ have clean block $Q/\lambda$ on an $s$-qubit system with $a$ block ancillas, where the known normalization satisfies $1\le\lambda\le2$. Suppose $U$ is unitary and $\|Q-U\|_{\mathrm{op}}\le\delta<1/4$. There is a finite amplification circuit, selected using $a,s,\lambda$ before $A_0,Q,U,\delta$, with exactly three calls to $A_0$ or its adjoint. Its unitary $C$ satisfies
--   $$\|CJ_{1+a,s}-J_{1+a,s}U\|_{\mathrm{op}}\le4\delta.$$
--   The embedding includes the added attenuation qubit and every original block ancilla. Both normalization endpoints and $\delta=0$ are included. This is a full clean-output estimate for an approximate block, not an exact-success-branch rotation identity.
--
--   Differences from the source:
--   - encoding: a supplied circuit and three calls to it or its adjoint → a macro-oracle circuit over elementary unitaries, chosen before the supplied circuit, with query count three; reason: the macro oracle represents the actual supplied finite circuit and all its calls are charged
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Lemma 5, p.11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=11; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_Amplification

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
open QAlgorithms
/-- Li--Wang, Lemma 5, p.11, Eq. (24), Appendix A p.39.
The output includes the added attenuation qubit even when delta is zero. -/
theorem one_round_oaa (a s : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) (hlam2 : lam ≤ 2) :
    ∃ c : AmplificationCircuit a s, c.queryCount 0 = 3 ∧
      ∀ (A₀ : Matrix (Qubits (a + s)) (Qubits (a + s)) ℂ)
        (Q U : Matrix (Qubits s) (Qubits s) ℂ) (δ : ℝ),
        IsQubitBlockEncoding a s A₀ lam 0 Q → U ∈ Matrix.unitaryGroup _ ℂ →
        opNorm (Q - U) ≤ δ → δ < 1 / 4 →
        let C := c.unitary (fun _ => A₀)
        C ∈ Matrix.unitaryGroup _ ℂ ∧
        opNorm (C * cleanQubitInput (1 + a) s - cleanQubitInput (1 + a) s * U) ≤ 4 * δ := by sorry
end SparseHamiltonianNorm.Simulation
