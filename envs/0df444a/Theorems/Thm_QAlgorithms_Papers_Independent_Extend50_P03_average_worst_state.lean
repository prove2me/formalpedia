-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_average_worst_state
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.average_worst_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:06:13.807192+00:00
-- url     : https://prove2.me/theorems/370f5e8d-fd29-462a-9cdd-ceebca86c833
-- title:
--   Appendix D: averaged basis outputs and worst averaged-state error
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. The actual integrable Haar average of $\mathcal E_U(|x\rangle\langle y|)$ is zero for $x\ne y$ and $\Pi_{|x|+\alpha}^{(n)}/\binom n{|x|+\alpha}$ for $x=y$. Its first-$t$-wire marginal is $\rho_{\rm avg}^{x,x}=\sum_{i=0}^t\Pi_i^{(t)}\binom{n-t}{|x|+\alpha-i}/\binom n{|x|+\alpha}$. Let $\zeta=\sum_i\beta_i\Pi_i^{(t)}$, where $\beta_i$ is the Eq.(27) coefficient, independent of $x$. Then
--
--   $$F(\rho_{\rm avg}^{x,x},\zeta)=\sum_{i=0}^t\binom ti\sqrt{\beta_i\frac{\binom{n-t}{|x|+\alpha-i}}{\binom n{|x|+\alpha}}}.$$
--
--   For fixed $a\in(0,1)$, exact $\alpha=an$, and $kt^2/n\to0$ with $k,t\ge1$, uniformly eventually $\left|\max_xP(\rho_{\rm avg}^{x,x},\zeta)/(k\sqrt t/(4n\sqrt{a(1-a)}))-1\right|\le Ckt^2/n$. This is an auxiliary averaged-basis error, distinct from reference-assisted channel worst error.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 25, Appendix D: averaged basis outputs and worst averaged-state error

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix D, PDF p.25: actual averaged basis matrix units, exact root
fidelity, and the auxiliary worst averaged-state expansion. The last printed
'1+(kt^2/n)' is changed to 1+O(kt^2/n): the cited Eq.(29)
has an asymptotic remainder and does not imply a finite exact coefficient. -/
theorem average_worst_state :
    (∀ n k alpha t : ℕ, ∀ A : Ancilla n k alpha, ∀ ht : t ≤ n,
      ∀ mu : Measure ((Matrix.unitaryGroup (Qubits n) ℂ)), ChargeHaar n mu → ∀ x y : Qubits k,
      let full := fun U => chargeEncoder A U (Matrix.single x y 1)
      let f := fun U => firstTrace n t ht (full U)
      Integrable full mu ∧ (∫ U, full U ∂mu) = averageEncodedUnit n alpha x y ∧
      Integrable f mu ∧ (∫ U, f U ∂mu) = averageMatrixUnit n alpha t x y) ∧
    (∀ n k alpha t : ℕ, k ≤ n → alpha ≤ n-k → t ≤ n → ∀ x : Qubits k,
      rootFidelity (averageBasis n alpha t x) (averageZeta n k alpha t) =
        ∑ i ∈ Finset.range (t+1), (t.choose i : ℝ) *
          Real.sqrt (averageSectorWeight n k alpha t i * chooseZ (n-t) ((hammingWeight x : ℤ)+alpha-i) /
            chooseZ n ((hammingWeight x : ℤ)+alpha))) ∧
    AverageWorstExpansion := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
