-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_exponentialStrongConverse
-- name    : QAlgorithms.Papers.Independent.Information100.P67.exponentialStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:49:50.883881+00:00
-- url     : https://prove2.me/theorems/363f4319-1aa6-489f-8026-dabc01cfead0
-- title:
--   Theorem 2.1 (Exponential strong converse)
-- statement:
--   Fix finite nonempty quantum systems $A,B,E$ and an isometric dilation $U:A\to B\otimes E$ of a degradable channel $\mathcal N$. Let $q_{\mathcal N}=\max_{\rho\in\mathcal S(A)}[H(\mathcal N(\rho))-H(\mathcal N^c(\rho))]$, with entropies in bits. For every $\Delta>0$, there are $\gamma>0$ and an integer $n_0\ge1$, depending only on this fixed channel and $\Delta$, such that every unassisted collective $(n,M)$ code with $n\ge n_0$ and $\log_2M\ge n(q_{\mathcal N}+\Delta)$ satisfies
--
--   $$f(\mathcal C_n)\le2^{-\gamma n},\qquad \varepsilon(\mathcal C_n),\ \varepsilon_{\max}(\mathcal C_n),\ \varepsilon_{\rm marg}(\mathcal C_n)\ge1-2^{-\gamma n}.$$
--
--   Here $f$ is the optimized squared fidelity to a uniform perfectly correlated classical key independent of one common normalized environment state; the other symbols denote the uniform optimized, maximal optimized, and actual-marginal joint infidelities. The operational capacities defined by achievable vanishing-error code sequences under all three criteria equal $q_{\mathcal N}$. This establishes exponential decay uniformly over all mixed message states and collective decoders.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 9, Theorem 2.1 (Exponential strong converse)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Theorem 2.1, PDF p.9 (proof pp.32–33): exponential converse with all
three errors and all three operational capacities. No input-rank restriction. -/
theorem exponentialStrongConverse [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U) :
    (∀ gap : ℝ, 0 < gap → ∃ gamma : ℝ, 0 < gamma ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n ≥ n0, ∀ code : PrivateCode A B n, code.Valid →
        (n : ℝ) * (maximumCoherentInformation U + gap) ≤ Real.logb 2 code.M →
        optimizedFidelity U code ≤ Real.rpow 2 (-gamma * n) ∧
        1 - Real.rpow 2 (-gamma * n) ≤ uniformError U code ∧
        1 - Real.rpow 2 (-gamma * n) ≤ maximalError U code ∧
        1 - Real.rpow 2 (-gamma * n) ≤ marginalError U code) ∧
    (∀ criterion, privateCapacity criterion U = maximumCoherentInformation U) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
