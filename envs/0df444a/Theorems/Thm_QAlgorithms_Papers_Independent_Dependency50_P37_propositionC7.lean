-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_propositionC7
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.propositionC7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:24:34.609119+00:00
-- url     : https://prove2.me/theorems/da15a178-1870-4193-94a8-5feabbbcb583
-- title:
--   Unital scrambling channels are fully irreducible
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Assume also $\Phi(I)=I$. A channel is fully irreducible when there are no equivalent projections $P,Q$, each different from $0,I$, and scalar $\lambda>0$ such that $\Phi(P)\le\lambda Q$. Equivalence of these projections means equal ranks, equivalently equal traces. Then
--
--   $$C_0(\Phi)=0\quad\Longrightarrow\quad\Phi\text{ is fully irreducible}.$$
--
--   The inequality between matrices uses the positive-semidefinite order. This relates loss of a perfect classical bit to the channel's action on projections.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 24, Proposition C.7

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

/-- Proposition C.7, PDF pp.24–25. Nontrivial excludes both zero and identity;
projection equivalence is equal rank, expressed by equality of their traces. -/
theorem propositionC7 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (hunital : Phi 1 = 1) (hscrambling : classicalCapacity Phi = 0) :
    FullyIrreducible Phi := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
