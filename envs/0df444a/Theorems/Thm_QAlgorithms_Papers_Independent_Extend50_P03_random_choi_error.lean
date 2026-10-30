-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_random_choi_error
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.random_choi_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:52:25.515108+00:00
-- url     : https://prove2.me/theorems/d919b410-99df-43f3-836d-5c87e713761d
-- title:
--   Theorem 1, Eqs. (9)–(10): mean and typical Choi error
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension.
--
--   Fix $a\in(0,1)$. Work along admissible integer sequences $n\to\infty$ with $k,t\ge1$ and $\alpha=an$ exactly. The constants below are positive and depend only on $a$, preceding the growth sequence, ancilla, and erased-wire choices; the eventual threshold may depend on the sequence. The displayed little-o ratio tends to zero. Expectations are integrable, and a probability bound allows a zero bad-event probability. Put $r=k^2t^2/n\to0$ and $B=\frac{\sqrt{tk}}{4n\sqrt{a(1-a)}}(1+Cr)$. Eventually,
--
--   $$\mathbb E_{H_\times}\varepsilon_{\rm Choi}\le B,\qquad H_\times\{U:\varepsilon_{\rm Choi}(U)>B\}\le e^{-cn}.$$
--
--   This gives both the mean and typical accuracy of the charge-conserving random encoder. For either excluded trivial case $k=0$ or $t=0$, the optimized error is exactly zero for every unitary encoder.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 8, Theorem 1, Eqs. (9)–(10): mean and typical Choi error

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Theorem 1, PDF pp.8–9, Eqs.(9)–(10): mean and typical optimized Choi error. -/
theorem random_choi_error :
    AsymptoticGuarantee ChargeHaar false ∧ ZeroErrorGuarantee false := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
