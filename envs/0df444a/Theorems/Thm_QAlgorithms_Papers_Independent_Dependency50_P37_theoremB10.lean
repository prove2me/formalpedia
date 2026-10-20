-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB10
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:19:35.330475+00:00
-- url     : https://prove2.me/theorems/1ef6f019-075a-4166-954d-76308956c4c8
-- title:
--   Three-capacity stabilization with corrected chain count
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Let $S_\Phi=\operatorname{span}_{i,j}\{K_i^*K_j\}$ for any Kraus representation. There is one positive integer $N$ satisfying
--
--   $$N\le d^2-\dim S_\Phi+1$$
--
--   such that, for every $n\ge0$, each of $Q_0,C_0,C_{0E}$ takes equal values at $\Phi^N$ and $\Phi^{N+n}$.
--
--   This is simultaneous stabilization of all three capacities.
--
--   **Formalization Note** The printed bound omits $+1$. There are $N-1$ strict increases starting with $S_\Phi$ at time $1$. A depolarizing qubit has full operator system and stabilizes first at time $1$, contradicting the printed bound $N\le0$.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 20, Theorem B.10

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Theorem B.10, PDF p.20, SOURCE CORRECTION: printed d^2-dim(S_Phi)
becomes d^2-dim(S_Phi)+1. The proof counts N-1 strict increases from time 1.
A depolarizing qubit has full operator system and requires N=1, refuting N<=0. -/
theorem theoremB10 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 - Module.finrank ℂ (graph Phi) + 1 ∧
      ∀ n : ℕ,
        quantumCapacity (Nat.iterate Phi N) = quantumCapacity (Nat.iterate Phi (N + n)) ∧
        classicalCapacity (Nat.iterate Phi N) = classicalCapacity (Nat.iterate Phi (N + n)) ∧
        assistedCapacity (Nat.iterate Phi N) = assistedCapacity (Nat.iterate Phi (N + n)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
