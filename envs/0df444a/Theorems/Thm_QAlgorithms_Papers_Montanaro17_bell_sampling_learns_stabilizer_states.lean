-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Montanaro17_bell_sampling_learns_stabilizer_states
-- name    : QAlgorithms.Papers.Montanaro17.bell_sampling_learns_stabilizer_states
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:10:06.873313+00:00
-- url     : https://prove2.me/theorems/0a09a432-7cec-4e34-966f-7aa3484dd399
-- title:
--   Bell sampling learns an unknown n-qubit stabilizer state with O(n) copies in time O(n^3)
-- statement:
--   This is Montanaro's theorem on learning stabilizer states by Bell sampling.
--
--   A stabilizer state of $n$ qubits is a unit vector $|\psi\rangle \in (\mathbb C^2)^{\otimes n}$ for which there is a commuting subgroup $G$ of the $n$-qubit Pauli group, not containing $-I$, with $|G| = 2^n$ and $M|\psi\rangle = |\psi\rangle$ for all $M \in G$. A learner proceeds in rounds; each round takes some fresh copies of the unknown state together with ancilla qubits in $|0\rangle$, applies a circuit of gates from $\{H, T, \mathrm{CNOT}\}$ whose gates may be switched on or off by bits computed (by Boolean circuits) from the outcomes of earlier rounds, and measures all its qubits in the computational basis. At the end a Boolean circuit maps all outcomes to a stabilizer tableau $\mathcal T$, i.e. $n$ signed Pauli strings $P_1, \dots, P_n$, whose associated projector is $\Pi_{\mathcal T} = \prod_{j} \tfrac12 (I + P_j)$. The time of the learner is the total number of quantum gates, ancilla qubits and classical Boolean gates.
--
--   There are constants $C > 0$, $c > 0$ and $N_0$ such that for every $n \ge N_0$ there is a single learner $L$, fixed independently of the unknown state, with the following properties:
--
--   1. every round of $L$ acts on at most two copies of the state;
--   2. $L$ uses at most $C n$ copies in total;
--   3. $L$ runs in time at most $C n^3$;
--   4. for every $n$-qubit stabilizer state $|\psi\rangle$,
--   $$
--   \Pr\big[\, L \text{ outputs } \mathcal T \text{ with } \Pi_{\mathcal T} = |\psi\rangle\langle\psi| \,\big] \;\ge\; 1 - e^{-c n}.
--   $$
--
--   The paper's Algorithm 1 achieves this with $5n+2$ copies (Bell sampling on $2n+1$ pairs, then single-copy Pauli measurements to fix the signs) and failure probability at most $2^{-n}$. The copy count matches the information-theoretic lower bound $\Omega(n)$ while acting on only two copies at a time.
--
--   **Formalization Note** Identification is up to global phase, as in the source: success is equality of the projector of the output tableau with $|\psi\rangle\langle\psi|$. The learner family over $n$ is not required to be uniformly generated, since the theorem names no uniformity notion.
-- source:
--   Learning stabilizer states by Bell sampling (Montanaro), arXiv:1707.04012v2, Theorem 1, PDF p. 1. https://arxiv.org/abs/1707.04012v2 . PDF SHA-256: e613468f2e48720f9f6dc03ddf91b78556377cc317239db08df2b295efbdb28c.

import Definitions.Def_QAlgorithms_Defs_StabilizerLearning
set_option autoImplicit false

namespace QAlgorithms.Papers.Montanaro17

open QAlgorithms

/-- Montanaro Theorem 1 (p.1; Algorithm 1 and its analysis, p.2). There is a quantum algorithm
which identifies an unknown stabilizer state `|ψ⟩` of `n` qubits given access to `O(n)` copies of
`|ψ⟩`; it makes collective measurements across at most two copies at a time, runs in time
`O(n³)` and fails with probability exponentially small in `n`.

Formalized: there are constants `C > 0`, `c > 0` and a threshold `N₀` such that for every
`n ≥ N₀` there is one learner `L` (chosen before the state) in which every round uses at most two
copies, the total number of copies is at most `C n`, the time is at most `C n³`, and for every
`n`-qubit stabilizer state `ψ` the learner outputs a tableau whose stabilizer projector is
`|ψ⟩⟨ψ|` (identification up to global phase, p.2) with probability at least `1 − e^{−cn}`.
(The proof gives `5n + 2` copies and failure probability `≤ 2^{−n}`, p.2.) -/
theorem bell_sampling_learns_stabilizer_states :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ L : CopyLearner n,
        (∀ k, L.copies k ≤ 2) ∧
        (L.copiesUsed : ℝ) ≤ C * n ∧
        (L.time : ℝ) ≤ C * (n : ℝ) ^ 3 ∧
        ∀ ψ : EuclideanSpace ℂ (Qubits n), IsStabilizerState ψ →
          L.successProb ψ ≥ 1 - Real.exp (-(c * n)) := by
  sorry

end QAlgorithms.Papers.Montanaro17
