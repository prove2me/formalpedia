-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_average_choi_asymptotics
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.average_choi_asymptotics
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:03:10.727184+00:00
-- url     : https://prove2.me/theorems/eb1a360d-4a68-4478-ad8a-0a9b073b3be8
-- title:
--   Appendix B: linear-charge averaged Choi fidelity and purified-distance expansion
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension.
--
--   Fix $a\in(0,1)$. Work along admissible integer sequences $n\to\infty$ with $k,t\ge1$ and $\alpha=an$ exactly. The constants below are positive and depend only on $a$, preceding the growth sequence, ancilla, and erased-wire choices; the eventual threshold may depend on the sequence. The displayed little-o ratio tends to zero. Expectations are integrable, and a probability bound allows a zero bad-event probability. Write $\rho_{RE}=\operatorname{Tr}_{n-t}\Phi_{\rm avg}$ for the constructed averaged EPR output, $\zeta_0=\operatorname{Tr}_R\rho_{RE}$, $F=F(\rho_{RE},I_R/2^k\otimes\zeta_0)$ and $P=P(\rho_{RE},I_R/2^k\otimes\zeta_0)$. The fidelity clause assumes $kt/n\to0$; the relative purified-distance clause separately assumes $k^2t^2/n\to0$. In their respective regimes, eventually
--
--   $$\left|F-\left(1-\frac{tk}{32a(1-a)n^2}\right)\right|\le C\frac{k^3t^3}{n^3},\qquad \left|\frac{P}{\sqrt{tk}/(4n\sqrt{a(1-a)})}-1\right|\le C\frac{k^2t^2}{n}.$$
--
--   These are two-sided expansions of the specific average-state comparison, not optimized decoder errors.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 23, Appendix B: linear-charge averaged Choi fidelity and purified-distance expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Appendix B, PDF pp.22–23: the fidelity expansion assumes kt=o(n).
The relative purified-distance expansion separately assumes k^2t^2=o(n).
Fidelity deficit has denominator n^2; both constants are uniform in the sequence. -/
theorem average_choi_asymptotics :
    ∀ a : ℝ, 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ → ChargeCodeParameters, LinearSequence a d →
      (Tendsto (fun i => ((d i).k : ℝ) * (d i).t / (d i).n) atTop (nhds 0) →
        ∃ N : ℕ, ∀ i ≥ N,
        let n := (d i).n; let k := (d i).k; let alpha := (d i).alpha; let t := (d i).t
        let F := rootFidelity (reducedAverage n k alpha t) (comparisonChoi n k alpha t)
        |F - (1 - (t : ℝ)*k/(32*a*(1-a)*(n : ℝ)^2))| ≤
          C*(k : ℝ)^3*(t : ℝ)^3/(n : ℝ)^3) ∧
      (Tendsto (fun i => relativeRemainder false (d i)) atTop (nhds 0) →
        ∃ N : ℕ, ∀ i ≥ N,
        let n := (d i).n; let k := (d i).k; let alpha := (d i).alpha; let t := (d i).t
        let P := purified (reducedAverage n k alpha t) (comparisonChoi n k alpha t)
        |P / leadingError false a (d i) - 1| ≤ C * relativeRemainder false (d i)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
