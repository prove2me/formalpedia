-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_worst_basis_min_entropy
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.worst_basis_min_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:04:29.558997+00:00
-- url     : https://prove2.me/theorems/e7a86908-8c25-4fb9-bba8-713a5ef78ca1
-- title:
--   Appendix C: basis-input min-entropy bounds
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. For a computational basis input $x$, put $q=|x|+\alpha$ and let $H_{\min}^x$ be the entropy of the actual Appendix C operator $\Lambda$ constructed from $x$ and the fixed ancilla, with trivial reference. Let $B=\sum_{i=0}^{n-t}\binom{t}{q-i}^2/\binom nq$, with signed out-of-range binomials zero. Then
--
--   $$-\log_2 B\le H_{\min}^x\le-\log_2\frac{B}{t+1}.$$
--
--   For the selected input, if $t\le q$ and $q\le n-t$, then $B=\binom{2t}{t}/\binom nq$. Uniformly over $x$ and the ancilla, in a fixed compact interior charge interval and this small-erasure regime with $k,t\ge1$, $H_{\min}^x=nH_2(q/n)-2t+O(\log n)$, and hence $H_{\min}^x\ge n\min\{H_2(\alpha/n),H_2((\alpha+k)/n)\}-2t-C\log_2(n+1)$. The finite formula also covers $t=0$.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 24, Appendix C: basis-input min-entropy bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix C, PDF pp.23–24: valid-sector finite sandwich, its interior
Vandermonde simplification guarded by t≤q≤n-t for the selected input,
and uniform two-sided basis entropy asymptotics. Printed: unguarded simplification.
Changed: require the full convolution range; at q=0 and t>0 it is truncated.
The numerator is sum_i binomial(t,q-i)^2, not a squared sum or 2^(2t). -/
theorem worst_basis_min_entropy :
    (∀ n k alpha t : ℕ, ∀ A : Ancilla n k alpha, t ≤ n → ∀ x : Qubits k,
      let q := hammingWeight x + alpha
      ((-Real.logb 2 (basisKappa n q t) : ℝ) : EReal) ≤ decouplingInputEntropy A t (ket x) ∧
      decouplingInputEntropy A t (ket x) ≤ ((-Real.logb 2 (basisKappa n q t/(t+1)) : ℝ) : EReal) ∧
      (t ≤ q → q ≤ n-t →
        basisKappa n q t = (Nat.choose (2*t) t : ℝ) / chooseZ n q)) ∧
    (∀ b : ℝ, 0 < b → b < 1/2 → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ d : ChargeCodeParameters, N ≤ d.n → Interior b d → ∀ A : Ancilla d.n d.k d.alpha,
      ∀ x : Qubits d.k,
      let h := (d.n : ℝ) * binEntropy2 (((hammingWeight x : ℝ)+d.alpha)/d.n) - 2*d.t
      ((h-C*Real.logb 2 (d.n+1) : ℝ) : EReal) ≤ decouplingInputEntropy A d.t (ket x) ∧
      decouplingInputEntropy A d.t (ket x) ≤ ((h+C*Real.logb 2 (d.n+1) : ℝ) : EReal) ∧
      ((d.n*endpointEntropy d-2*d.t-C*Real.logb 2 (d.n+1) : ℝ) : EReal) ≤
        decouplingInputEntropy A d.t (ket x)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
