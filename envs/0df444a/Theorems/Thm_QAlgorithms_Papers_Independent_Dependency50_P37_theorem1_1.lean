-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theorem1_1
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:07:48.538647+00:00
-- url     : https://prove2.me/theorems/65859d06-f7bd-43cb-b95a-735182df2d4e
-- title:
--   Eventual scrambling characterizes mixing and asymptotic entanglement breaking
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   A semigroup is eventually classical or quantum scrambling when the corresponding capacity vanishes at some positive time. It is mixing if some density $\rho$ satisfies $\Phi^n(X)\to\operatorname{Tr}(X)\rho$ for every operator $X$. It is asymptotically entanglement breaking when every channel limit along an unbounded sequence of times breaks entanglement with every finite reference system. Then
--
--   $$
--   \begin{aligned}
--   \Phi\text{ eventually quantum scrambling}&\iff\Phi\text{ asymptotically entanglement breaking},\\
--   \Phi\text{ eventually classical scrambling}&\iff\Phi\text{ mixing}.
--   \end{aligned}
--   $$
--
--   These equivalences characterize precisely when perfect storage eventually becomes impossible.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 3, Theorem 1.1

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

/-- Theorem 1.1, PDF pp.2–3: both eventual-scrambling equivalences. -/
theorem theorem1_1 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    (EventuallyQuantumScrambling Phi ↔ AsymptoticallyEntanglementBreaking Phi) ∧
    (EventuallyClassicalScrambling Phi ↔ Mixing Phi) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
