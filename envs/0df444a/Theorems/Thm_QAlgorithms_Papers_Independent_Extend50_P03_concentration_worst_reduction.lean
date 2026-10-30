-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_concentration_worst_reduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.concentration_worst_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:53:15.40848+00:00
-- url     : https://prove2.me/theorems/0b86bbde-e1d4-456c-a652-2d78ed4fa937
-- title:
--   Lemma 2, Eq. (16): concentration-to-worst-error reduction
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Let $n\to\infty$ and fix $b\in(0,1/2)$ such that eventually $b\le\alpha/n\le(\alpha+k)/n\le1-b$, $1\le k,t$, and $t\le\min(\alpha,n-\alpha-k)$. Write $h=\min\{H_2(\alpha/n),H_2((\alpha+k)/n)\}$, where $H_2$ is binary entropy. There are $C>0$ and an integer $D\ge0$, uniform in the ancilla, erasure set and logical basis inputs, such that eventually the following holds. For $\epsilon\ge0$, $\delta,\delta'>0$, if one normalized state $\zeta$ independent of $x$ satisfies $P(\rho_{\rm avg}^{x,x},\zeta)\le\epsilon$ for every computational basis string $x$, then
--
--   $$\Pr\!\left[\varepsilon_{\rm worst}>\epsilon+\delta+2^k\sqrt{\delta'}\right]\le Cn^D\left(\frac{2^{k-nh/4+t/2}}\delta+\frac{2^{2k-nh/2+t}}{\delta'}\right).$$
--
--   Here $\rho_{\rm avg}^{x,x}$ is the constructed Haar-averaged erased-register output. This is a concentration-to-recovery reduction; the right side need not be at most one.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 10, Lemma 2, Eq. (16): concentration-to-worst-error reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Lemma 2, PDF pp.10–11, Eq.(16): retain n/4, n/2, and the conservative
2^k sqrt(deltaPrime). The Appendix C regime is explicit in the guarantee. -/
theorem concentration_worst_reduction : ConcentrationGuarantee ChargeHaar := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
