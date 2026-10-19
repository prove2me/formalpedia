-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapO03_lowRankGibbs_sampling
-- name    : QAlgorithms.Papers.RoadmapO03.lowRankGibbs_sampling
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:28:21.709425+00:00
-- url     : https://prove2.me/theorems/eaa62ab0-f92a-42d6-bc9e-218e399ac487
-- title:
--   Low-rank Gibbs sampling from indexed quantum inputs, with address costs
-- statement:
--   Let $n,m\geq1$, let $\varnothing\ne S\subseteq[m]$, and let $c_j>0$ for $j\in S$. Let $A_j^+,A_j^-\in\mathbb C^{n\times n}$ be positive semidefinite, and set
--   $$
--   K^\pm=\sum_{j\in S}c_jA_j^\pm,\qquad K=K^+-K^-.
--   $$
--   Assume $\operatorname{rank}(K^+),\operatorname{rank}(K^-)\leq r_K$ and $\operatorname{Tr}(K^+)+\operatorname{Tr}(K^-)\leq B_K$, with $r_K\in\mathbb N$, $B_K\geq0$, and $\epsilon>0$.
--
--   Oracle D.1 and its inverse write exact binary representations of both component traces at initialized answer registers. Oracle D.2 and its inverse jointly prepare arbitrary normalized purifications of $A_j^\pm/\operatorname{Tr}(A_j^\pm)$ when that trace is nonzero. At trace zero they prepare arbitrary normalized states, whose zero-weight contributions are ignored. All other finite-register actions, purification phases, and actions on unused qubit labels are arbitrary. Each source tensor factor is separately encoded in binary, in the displayed source order. The actual supplied qubit oracles must restrict to these finite-register unitaries; a known identity extension or controlled black-box operation is not assumed.
--
--   There are absolute $C>0$ and $q\in\mathbb N$ such that, for each public $n,m,S,c,r_K,B_K,\epsilon$ and binary trace format, a sampler and workspace can be chosen before the hidden PSD matrices and before all compatible oracle unitaries. It terminates almost surely, has a summable unconditional output density $\sigma$, and satisfies
--   $$
--   \left\|\sigma-\frac{e^{-K}}{\operatorname{Tr}(e^{-K})}\right\|_{\mathrm{Tr}}\leq\epsilon,
--   \qquad
--   \mathbb E[G+Q_{\mathrm{D.1}}+Q_{\mathrm{D.2}}]
--   \leq C|S|(1+\log m)(1+\log n+r_K+B_K+\epsilon^{-1})^q.
--   $$
--   Here $G$ counts one- and two-qubit gates, preparations and measurements, and $Q$ counts actual oracle or inverse calls. Finite classical draws are free in this model. The same bound holds with any $\Phi\geq|S|$ in place of $|S|$.
--
--   **Printed / changed / why.** Lemma 12 prints $|S|\operatorname{poly}(\log n,r_K,B_K,\epsilon^{-1})$. The corrected elementary-gate statement includes $1+\log m$ to charge preparation of an indexed-oracle address, and excludes empty support to avoid a literal zero-cost maximally mixed state. Zero components are retained according to the paper's own application on p.29; the arbitrary-state convention completes the otherwise undefined normalized quotient without changing any nonzero component. Precision uses the unhalved trace norm in Eqs. (F.15)–(F.17); expected repetition is stated on p.33.
--
--   **Correction to the printed source.**
--
--   Printed: For S subset [m], Lemma 12 gives |S| * poly(log n, r_K, B_K, epsilon inverse) quantum gates and D.1/D.2 queries; D.2 writes A_j^sign / Tr(A_j^sign) without a zero-trace convention.
--
--   Corrected: Require S nonempty and include an elementary address-cost factor 1 + log m in both the |S| bound and its Phi corollary. Permit arbitrary normalized D.2 outputs for zero PSD components and arbitrary unitary completions on unused qubit labels, preserving the promises on every nonzero component.
--
--   Reason: The all-zero initialized elementary-gate model must prepare an m-valued address: for singleton S at a distant index this requires Omega(log m) one- or two-qubit gates, while the printed bound has no m dependence. Empty S makes the printed bound zero although K=0 has Gibbs state I/n, which is mixed for n>1. The paper explicitly applies Lemma 12 with zero components on p.29, and Lemma 11 assigns them zero selection probability; excluding them drops source cases. No nonzero quotient, Gibbs target, rank/trace bound, oracle count, accuracy, or quantifier order is changed.
-- source:
--   Quantum SDP Solvers: Large Speed-ups, Optimality, and Applications to Quantum Learning, arXiv:1710.02581v3, Appendix D.5, Lemma 12, PDF p. 26. https://arxiv.org/abs/1710.02581v3 . PDF SHA-256: bc6265c9c89c31b96fe2edb5627588f8e0addbba969e9bde42ebfdf8546d6791.

import Definitions.Def_QAlgorithms_Defs_JointLowRankGibbsContracts
import Definitions.Def_QAlgorithms_Papers_RoadmapO03_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapO03

open QAlgorithms.LowRankGibbs






/-- Low-rank Gibbs sampling from indexed quantum inputs: arXiv:1710.02581v3,
Appendix D.5, Lemma 12, PDF p.26, using Lemma 11 and Appendix G.3, Theorem 4,
PDF pp.38–40 (also Appendix F.2, p.32). Zero PSD components have arbitrary
normalized purification outputs, ignored at zero sampling weight (p.29 and Lemma 11).
Printed / changed / why: the printed |S| * poly(log n, rK, BK, eps inverse) gate
bound omits address preparation. We include a factor 1 + log m to charge elementary
gates for the index register, and require nonempty S to avoid the printed zero-cost
bound for preparing I/n at empty support. All other conclusions are retained.
Unused qubit labels have arbitrary unitary completions, rather than a known identity.
The output is unconditional, with almost-sure termination and expected charged cost
(PDF p.33). Precision is the unhalved trace norm of Eqs. (F.15)–(F.17), p.34.
The last clause records the corrected corollary for every support bound Phi. -/
theorem lowRankGibbs_sampling :
    ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
    ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ (S : Finset (Fin m)), S.Nonempty →
    ∀ (c : Fin m → ℝ), (∀ j ∈ S, 0 < c j) →
    ∀ (rK : ℕ) (BK eps : ℝ), 0 ≤ BK → 0 < eps →
    ∀ F : TraceBinaryFormat,
    ∃ (N w : ℕ) (P : SamplingProgram (inputArities n m F) N n w),
    ∀ A : PSDInputFamily n m,
      (weightedPlus A S c).rank ≤ rK →
      (weightedMinus A S c).rank ≤ rK →
      (weightedPlus A S c).trace.re + (weightedMinus A S c).trace.re ≤ BK →
    ∀ (Otr : Matrix (Fin m × (Qubits F.width × Qubits F.width))
        (Fin m × (Qubits F.width × Qubits F.width)) ℂ)
      (Oprep : Matrix (Fin m × ((Fin n × Fin n) × (Fin n × Fin n)))
        (Fin m × ((Fin n × Fin n) × (Fin n × Fin n))) ℂ),
      IsTraceInputOracle A F Otr → IsJointPurificationInputOracle A Oprep →
    ∀ O : (k : Fin 2) → Matrix (Qubits (inputArities n m F k))
      (Qubits (inputArities n m F k)) ℂ,
      IsInputOracles Otr Oprep O →
      GibbsSamplingContract P O (weightedHamiltonian A S c) eps ∧
      (∑ j : Fin 3, expectedResources P O j) ≤
        ENNReal.ofReal (C * S.card * (1 + Real.log m) *
          (1 + Real.log n + rK + BK + eps⁻¹) ^ q) ∧
      ∀ Phi : ℕ, S.card ≤ Phi →
        (∑ j : Fin 3, expectedResources P O j) ≤
          ENNReal.ofReal (C * Phi * (1 + Real.log m) *
            (1 + Real.log n + rK + BK + eps⁻¹) ^ q) := by sorry

end QAlgorithms.Papers.RoadmapO03
