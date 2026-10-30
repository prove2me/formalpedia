-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_choi_min_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.choi_min_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:00:20.831335+00:00
-- url     : https://prove2.me/theorems/d65c937a-3f9d-42f3-97fc-2855f54f42ae
-- title:
--   Appendix A, Eq. (26): finite Choi min-entropy sandwich and linear-charge estimate
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Form the actual partial-decoupling operator $\Lambda=F(\Psi\otimes\tau)F^\dagger$ of Appendix A, with $\Psi$ equal to $k$ normalized EPR pairs appended with $\psi_\alpha$, $\tau$ the normalized Choi state of the channel retaining $t$ wires, and $F=\bigoplus_q\sqrt{2^n/\binom nq}(\Pi_q\otimes\Pi_q)$. Entropy is $H_{\min}(P|Q)=-\log_2 s(\Lambda)$, extended to $+\infty$ at a zero SDP optimum. Define
--
--   $$\kappa=\sum_{i=0}^{n-t}\left(\sum_{j=0}^k\frac{\binom{t}{j+\alpha-i}\binom{k}{j}}{\sqrt{2^k\binom{n}{j+\alpha}}}\right)^2.$$
--
--   Out-of-range signed binomials vanish. Then $\kappa>0$ and $-\log_2\kappa\le H_{\min}\le-\log_2(\kappa/(k+t+1))$. For fixed $a\in(0,1)$ and exact $\alpha=an$, with every legal $k,t$ (including $\alpha+k=n$), $H_{\min}\ge n\min\{H_2(\alpha/n),H_2((\alpha+k)/n)\}-2t-k-C\log_2(n+1)$ uniformly, without a small-erasure restriction on this clause. In particular, at fixed $a\in(0,1)$, exact $\alpha=an$, and $k,t\ge1$, the regime $k^2t^2=O(n)$ gives $H_{\min}\ge cn$ eventually. This controls the partial-decoupling term.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 20, Appendix A, Eq. (26): finite Choi min-entropy sandwich and linear-charge estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix A, PDF pp.19–20, Eq.(26): finite constructed-state sandwich, plus
the linear-hammingCharge entropy-growth clause. No entropy bound is a hypothesis. -/
theorem choi_min_entropy :
    (∀ n k alpha t : ℕ, ∀ A : Ancilla n k alpha, t ≤ n →
      0 < choiSectorKappa n k alpha t ∧
      ((-Real.logb 2 (choiSectorKappa n k alpha t) : ℝ) : EReal) ≤ choiEntropy A t ∧
      choiEntropy A t ≤ ((-Real.logb 2 (choiSectorKappa n k alpha t / (k+t+1)) : ℝ) : EReal)) ∧
    ChoiEntropyGrowth ∧ ChoiEntropyLinear := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
