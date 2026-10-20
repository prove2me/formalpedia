-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_scramblingAdjointPositivity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.scramblingAdjointPositivity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:26:13.082798+00:00
-- url     : https://prove2.me/theorems/1832a910-7572-4915-8c1c-e6285565c139
-- title:
--   Scrambling implies strict positivity of the adjoint composition
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Let $\Phi^*$ be the Hilbert–Schmidt adjoint. A map is strictly positive when every nonzero positive-semidefinite input has positive-definite output. If $\Phi$ is scrambling, then
--
--   $$\Phi^*\circ\Phi\text{ is strictly positive}.$$
--
--   Consequently, if also $\Phi^*=\Phi$, then $\Phi^2$ is strictly positive.
--
--   This gives an immediate positivity statement for self-adjoint scrambling channels. The first composition is treated as a CP map; it is not asserted to be trace preserving without unitality.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 25, §C.2, unnumbered adjoint positivity remark

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

/-- Section C.2 remark, PDF pp.25–26: Phi* Phi is strictly positive as a CP map;
it is not asserted to be trace preserving without unitality. -/
theorem scramblingAdjointPositivity {d : ℕ} (hd : 0 < d) (Phi : Dynamics d)
    (hPhi : IsChannel Phi) (hscrambling : classicalCapacity Phi = 0) :
    StrictlyPositive (adjoint Phi ∘ Phi) ∧
    (adjoint Phi = Phi → StrictlyPositive (Nat.iterate Phi 2)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
