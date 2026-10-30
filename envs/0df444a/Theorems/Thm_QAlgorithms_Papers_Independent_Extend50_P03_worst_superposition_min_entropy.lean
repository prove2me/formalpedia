-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_worst_superposition_min_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.worst_superposition_min_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:05:14.21689+00:00
-- url     : https://prove2.me/theorems/aca9e9db-06a4-4df2-9657-cd511ea8c031
-- title:
--   Appendix C: two-basis-superposition entropy estimate
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Fix a compact interior charge interval, with $k,t\ge1$ and $t\le\min(\alpha,n-\alpha-k)$. For distinct computational basis strings $x,y$, form any of the four normalized vectors $v=(|x\rangle\pm|y\rangle)/\sqrt2$ or $v=(|x\rangle\pm i|y\rangle)/\sqrt2$. Let $H_{\min}^v$ be the entropy of the actual Appendix C partial-decoupling operator constructed from $v$ appended with $\psi_\alpha$, with trivial reference. Uniformly over the strings, four choices and ancilla, eventually
--
--   $$H_{\min}^v\ge n\min\{H_2((|x|+\alpha)/n),H_2((|y|+\alpha)/n)\}-2t-C\log_2(n+1).$$
--
--   It is also at least $n\min\{H_2(\alpha/n),H_2((\alpha+k)/n)\}-2t-C\log_2(n+1)$. This is the lower estimate used in Lemma 2; no universal preliminary finite chi sandwich is asserted.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 24, Appendix C: two-basis-superposition entropy estimate

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix C, PDF p.24: final uniform lower estimate for all four normalized
two-basis superpositions. Avoid the preliminary ambiguous finite chi sandwich
and the printed minus-alpha denominators in its closed-form line. -/
theorem worst_superposition_min_entropy :
    ∀ b : ℝ, 0 < b → b < 1/2 → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ d : ChargeCodeParameters, N ≤ d.n → Interior b d → ∀ A : Ancilla d.n d.k d.alpha,
      ∀ x y : Qubits d.k, x ≠ y → ∀ imaginary negative : Bool,
      let h := (d.n : ℝ) * min
        (binEntropy2 (((hammingWeight x : ℝ)+d.alpha)/d.n))
        (binEntropy2 (((hammingWeight y : ℝ)+d.alpha)/d.n)) - 2*d.t - C*Real.logb 2 (d.n+1)
      ((h : ℝ) : EReal) ≤ decouplingInputEntropy A d.t (twoBasis x y imaginary negative) ∧
      ((d.n*endpointEntropy d-2*d.t-C*Real.logb 2 (d.n+1) : ℝ) : EReal) ≤
        decouplingInputEntropy A d.t (twoBasis x y imaginary negative) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
