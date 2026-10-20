-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_fixedStateBitCode
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.fixedStateBitCode
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:15:04.846916+00:00
-- url     : https://prove2.me/theorems/b6dea7f2-e821-43cc-b75f-f7b4f8a9cd5d
-- title:
--   Constructed fixed-state encoding of a persistent bit
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Let $\rho\ne\sigma$ be invariant density matrices. Put $A=\rho-\sigma$, $A_+=\max(A,0)$, $A_-=\max(-A,0)$ by Hermitian functional calculus, and $\gamma_\pm=A_\pm/\operatorname{Tr}A_\pm$. Both traces are positive, both Jordan parts are fixed by $\Phi$, and $\gamma_\pm$ are density matrices satisfying
--
--   $$
--   \Phi^n(\gamma_\pm)=\gamma_\pm,\qquad
--   \operatorname{Tr}\bigl(\Phi^n(\gamma_+)\Phi^n(\gamma_-)\bigr)=0
--   \quad(n\ge0).
--   $$
--
--   Thus these explicitly constructed states encode a bit recoverable at every time.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 16, §B.2 Case I, unnumbered fixed-state encoding

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

/-- Section B.2 Case I, PDF p.16: the code is constructed from the Jordan parts
of rho-sigma. Positive trace denominators, normalization, invariance, and all-time
orthogonality are conclusions, not hypotheses on arbitrary desired code states. -/
theorem fixedStateBitCode {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (rho sigma : Operator d) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hne : rho ≠ sigma) (hfixrho : Phi rho = rho) (hfixsigma : Phi sigma = sigma) :
    let A := rho - sigma
    let plus := positivePart A
    let minus := positivePart (-A)
    let gamma1 := normalizedPositivePart A
    let gamma2 := normalizedPositivePart (-A)
    0 < plus.trace.re ∧ 0 < minus.trace.re ∧
    Phi plus = plus ∧ Phi minus = minus ∧
    IsDensityMatrix gamma1 ∧ IsDensityMatrix gamma2 ∧
    ∀ n : ℕ, Nat.iterate Phi n gamma1 = gamma1 ∧ Nat.iterate Phi n gamma2 = gamma2 ∧
      OrthogonalOutputs (Nat.iterate Phi n gamma1) (Nat.iterate Phi n gamma2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
