-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_operatorSystemStabilization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.operatorSystemStabilization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:12:43.454935+00:00
-- url     : https://prove2.me/theorems/4e6a947b-f556-44ac-babd-603be2c38f18
-- title:
--   Operator-system growth and finite stabilization
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   For a Kraus representation $\Phi(X)=\sum_i K_iXK_i^*$, let $S_{\Phi}=\operatorname{span}_{i,j}\{K_i^*K_j\}$. The systems increase with positive iteration time. There is a first stabilization time $N$ such that
--
--   $$
--   1\le N\le d^2-\dim S_\Phi+1\le d^2,\qquad
--   S_{\Phi^N}=S_{\Phi^{N+n}}\quad(n\ge0),
--   $$
--
--   and $S_{\Phi^j}\subsetneq S_{\Phi^{j+1}}$ for $1\le j<N$.
--
--   This identifies the finite-dimensional mechanism underlying capacity stabilization.
--
--   **Formalization Note** The refined count includes the missing $+1$ in the printed B.10; strictness is asserted only before the first equality.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 4, §1.2, unnumbered operator-system stabilization

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

/-- Section 1.2, PDF pp.4,20: strict growth only before first stabilization.
The refined bound includes the missing +1 in B.10: N-1 strict increases start at S_Phi. -/
theorem operatorSystemStabilization {d : ℕ} (hd : 0 < d) (Phi : Dynamics d)
    (hPhi : IsChannel Phi) :
    (∀ n : ℕ, 0 < n → graph (Nat.iterate Phi n) ≤ graph (Nat.iterate Phi (n + 1))) ∧
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 ∧
      N ≤ d ^ 2 - Module.finrank ℂ (graph Phi) + 1 ∧
      (∀ n : ℕ, 0 < n → n < N →
        graph (Nat.iterate Phi n) < graph (Nat.iterate Phi (n + 1))) ∧
      ∀ n : ℕ, graph (Nat.iterate Phi N) = graph (Nat.iterate Phi (N + n)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
