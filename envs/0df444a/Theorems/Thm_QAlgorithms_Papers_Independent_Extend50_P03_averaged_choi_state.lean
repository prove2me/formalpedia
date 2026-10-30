-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_averaged_choi_state
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.averaged_choi_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:02:22.796707+00:00
-- url     : https://prove2.me/theorems/37d9c4f8-dd01-403c-aabc-04ef11f414cf
-- title:
--   Appendix B, Eqs. (27)–(28): averaged state and exact fidelity
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Let $\Pi_j^{(m)}$ be the weight-$j$ projector on $m$ qubits and define $\Phi_{\rm avg}=\mathbb E_U(\mathrm{id}_R\otimes\mathcal E_U)(\widehat\phi^{(k)})$, with $R$ first. Its explicit form is $2^{-k}\sum_{j=0}^k\Pi_j^{(k)}\otimes\Pi_{j+\alpha}^{(n)}/\binom{n}{j+\alpha}$. Put $\rho_{RE}=\operatorname{Tr}_{n-t}\Phi_{\rm avg}$, $\zeta_0=\operatorname{Tr}_R\rho_{RE}=\sum_i\beta_i\Pi_i^{(t)}$, and $\beta_i=2^{-k}\sum_{j=0}^k\binom kj\binom{n-t}{j+\alpha-i}/\binom n{j+\alpha}$. Then
--
--   $$F(\rho_{RE},I_R/2^k\otimes\zeta_0)=2^{-k}\sum_{j=0}^k\sum_{i=0}^t\binom kj\binom ti\sqrt{\beta_i\frac{\binom{n-t}{j+\alpha-i}}{\binom n{j+\alpha}}}.$$
--
--   The expectation is integrable; the theorem identifies its marginal with the constructed sector sum. Signed invalid binomial indices contribute zero. This exact finite identity supports the asymptotic expansions.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 21, Appendix B, Eqs. (27)–(28): averaged state and exact fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix B, PDF pp.20–21, Eqs.(27)–(28): identify the actual Haar average,
its actual partial trace and marginal, and the exact root fidelity. Signed
j+alpha-i is never truncated. -/
theorem averaged_choi_state {n k alpha t : ℕ} (A : Ancilla n k alpha)
    (ht : t ≤ n) (mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ))) (hmu : ChargeHaar n mu) :
    let f := fun U => idTensorSuperop (R := Qubits k) (chargeEncoder A U) (pureDensity (maxEntangled k))
    Integrable f mu ∧ (∫ U, f U ∂mu) = averageChoi n k alpha ∧
    idTensorSuperop (R := Qubits k) (firstTrace n t ht) (averageChoi n k alpha) =
      reducedAverage n k alpha t ∧
    traceLeft (reducedAverage n k alpha t) = averageZeta n k alpha t ∧
    rootFidelity (reducedAverage n k alpha t) (comparisonChoi n k alpha t) =
      ((2 : ℝ)^k)⁻¹ * ∑ j ∈ Finset.range (k+1), ∑ i ∈ Finset.range (t+1),
        (k.choose j : ℝ) * (t.choose i : ℝ) *
          Real.sqrt (averageSectorWeight n k alpha t i * chooseZ (n-t) ((j : ℤ)+alpha-i) /
            chooseZ n ((j : ℤ)+alpha)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
