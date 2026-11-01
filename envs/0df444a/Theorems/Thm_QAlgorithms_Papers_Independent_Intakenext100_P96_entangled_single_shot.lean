-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P96_entangled_single_shot
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P96.entangled_single_shot
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:49:32.134449+00:00
-- url     : https://prove2.me/theorems/49204190-f721-4f6a-88a4-e70c7d875a7e
-- title:
--   Optimal joint single-shot test and four probabilities
-- statement:
--   Work in the retained vacuum/single-photon model, on a signal space with vacuum $|\mathrm{vac}\rangle$ and $d\ge1$ orthogonal single-photon modes. Let $b\ge0$ be the background probability per mode, with $db\le1$, and let $0\le\eta\le1$ be the reflection probability. Set
--   $$
--   \rho_0=(1-db)|\mathrm{vac}\rangle\langle\mathrm{vac}|+b\sum_{k=1}^d|k\rangle\langle k|.
--   $$
--
--   Use the resource $|\Phi_d\rangle=d^{-1/2}\sum_{k=1}^d|k\rangle_S|k\rangle_A$, transmitting only the signal and retaining the ancillary photon perfectly. Write $P_\Phi=|\Phi_d\rangle\langle\Phi_d|$, $\sigma_0=\rho_0\otimes I_A/d$, and $\sigma_1=(1-\eta)\sigma_0+\eta P_\Phi$.
--   With equal prior probabilities, the ideal joint measurement $\{P_\Phi,I-P_\Phi\}$, guessing present on yes, minimizes error among all binary effects on signal and ancilla. The four conditional probabilities are
--   $$
--   \begin{aligned}
--   p_e(\mathrm{no}\mid0)&=1-b/d,&p_e(\mathrm{yes}\mid0)&=b/d,\\
--   p_e(\mathrm{no}\mid1)&=(1-b/d)(1-\eta),&
--   p_e(\mathrm{yes}\mid1)&=(1-\eta)b/d+\eta .
--   \end{aligned}
--   $$
--   The labels $0,1$ denote absence and presence. These probabilities express the effective background reduction from $b$ to $b/d$.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, PDF p. 7, Optimal joint single-shot test and four conditional probabilities (9)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96

noncomputable section

open Filter

open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6--7, (9): the ideal Phi_d joint projector is an optimal equal-prior
single-shot test, with all four displayed conditional probabilities. -/
theorem entangled_single_shot (p : ModelParameters) :
    IsEffect (pairTest p.d) ∧
    (∀ M : Matrix (SignalIndex p.d × Fin p.d) (SignalIndex p.d × Fin p.d) ℂ,
      IsEffect M →
      binaryError (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta) (pairTest p.d) ≤
        binaryError (pairAbsent p.d p.b) (pairPresent p.d p.b p.eta) M) ∧
    effectProb (1 - pairTest p.d) (pairAbsent p.d p.b) = 1 - p.b / (p.d : ℝ) ∧
    effectProb (1 - pairTest p.d) (pairPresent p.d p.b p.eta) =
      (1 - p.b / (p.d : ℝ)) * (1 - p.eta) ∧
    effectProb (pairTest p.d) (pairAbsent p.d p.b) = p.b / (p.d : ℝ) ∧
    effectProb (pairTest p.d) (pairPresent p.d p.b p.eta) =
      (1 - p.eta) * (p.b / (p.d : ℝ)) + p.eta := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P96

end
