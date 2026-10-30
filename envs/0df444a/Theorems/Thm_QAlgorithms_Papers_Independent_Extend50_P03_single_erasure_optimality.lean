-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_single_erasure_optimality
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.single_erasure_optimality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:57:32.22108+00:00
-- url     : https://prove2.me/theorems/0fb11e2f-784d-4fbf-9e2f-e06271b626d1
-- title:
--   §5: leading-order optimality for one random erased qubit
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Consider uniformly random single-qubit erasure with the location flag. For every covariant CPTP encoding with $n>0$, write $\ell_k=\binom{k}{\lceil k/2\rceil}\lceil k/2\rceil/2^k$. The lower bounds cited from Faist et al. [11] and the paper's upper bounds give
--
--   $$\varepsilon_{\rm Choi}\ge\ell_k/n,\quad\varepsilon_{\rm worst}\ge k/(2n);\qquad \varepsilon_{\rm Choi}\le\frac{\sqrt k}{2n}(1+O(k^2/n)),\quad\varepsilon_{\rm worst}\le\frac{k}{2n}(1+O(k/n)).$$
--
--   The upper bounds hold in mean and with exponentially high probability at even $n$, $\alpha=n/2$, respectively under $k^2=o(n)$ and $k=o(n)$. In the worst metric the mean divided by $k/(2n)$ tends to one for every such growing-$k$ sequence; for Choi the analogous equality holds when $k=1$. Moreover $\ell_1=1/2$ and $(\sqrt k/2)/\ell_k\to\sqrt{\pi/2}$ as $k\to\infty$. This is leading-order optimality for the stated flagged noise model, not a lower bound for an arbitrary fixed site.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 13, §5: leading-order optimality for one random erased qubit

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Section 5, PDF p.13: [11]'s cited lower bounds concern a uniformly random,
flagged erased qubit. The resulting mean worst coefficient is optimal for growing
k=o(n); the Choi coefficient is exact at k=1 and within asymptotic sqrt(pi/2) for
large k. Upper/typical bounds for growing k are those of Theorems 1–2. -/
theorem single_erasure_optimality :
    (∀ n k : ℕ, 0 < n → k ≤ n → ∀ E : Superop (Qubits k) (Qubits n),
      IsChannel E → U1ChargeCovariant E →
      choiLowerCoefficient k / n ≤ optimizedCodeError false (flaggedPatternErasure (singleErasureLaw n) ∘ E) ∧
      (k : ℝ)/(2*n) ≤ optimizedCodeError true (flaggedPatternErasure (singleErasureLaw n) ∘ E)) ∧
    OptimalSingleLimit true ∧ OptimalSingleLimit false ∧
    PatternGuarantee ChargeHaar ∧
    choiLowerCoefficient 1 = 1/2 ∧
    Tendsto (fun k : ℕ => (Real.sqrt (k+1)/2) / choiLowerCoefficient (k+1))
      atTop (nhds (Real.sqrt (Real.pi/2))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
