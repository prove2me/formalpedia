-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_constant_charge_min_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.constant_charge_min_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:01:17.994478+00:00
-- url     : https://prove2.me/theorems/b52c6996-e9d8-41a3-9c93-7582ba65da82
-- title:
--   Appendix A: fixed-charge Choi entropy estimate
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Fix nonnegative integers $\alpha,k,t$ independently of $n$. Let $H_{\min}$ be the conditional min-entropy of the constructed Appendix A Choi partial-decoupling operator $F(\Psi\otimes\tau)F^\dagger$, with $\Psi$ the normalized EPR/ancilla input and $\tau$ the erasure complementary-channel Choi state. There are $C>0$ and $N$ independent of the normalized charge-$\alpha$ ancilla such that for every admissible $n\ge N$,
--
--   $$H_{\min}\ge\alpha\log_2 n-C.$$
--
--   For $\alpha=0$ this is a bounded lower estimate, not an assertion of exponential decoupling or a same-order bound on optimized channel error.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 20, Appendix A: fixed-charge Choi entropy estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix A, PDF p.20: fixed alpha,k,t, in a different regime from alpha=an.
At alpha=0 this gives only a bounded lower estimate. -/
theorem constant_charge_min_entropy (alpha k t : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ A : Ancilla n k alpha,
      t ≤ n → (((alpha : ℝ)*Real.logb 2 n - C : ℝ) : EReal) ≤ choiEntropy A t := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
