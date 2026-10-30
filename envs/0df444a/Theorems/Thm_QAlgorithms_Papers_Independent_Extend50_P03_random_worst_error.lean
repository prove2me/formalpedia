-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_random_worst_error
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.random_worst_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:54:09.44213+00:00
-- url     : https://prove2.me/theorems/4f090b82-c7f0-4089-ad7e-4f4174ac4e93
-- title:
--   Theorem 2, Eqs. (19)–(20): mean and typical worst-case error
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension.
--
--   Fix $a\in(0,1)$. Work along admissible integer sequences $n\to\infty$ with $k,t\ge1$ and $\alpha=an$ exactly. The constants below are positive and depend only on $a$, preceding the growth sequence, ancilla, and erased-wire choices; the eventual threshold may depend on the sequence. The displayed little-o ratio tends to zero. Expectations are integrable, and a probability bound allows a zero bad-event probability. Put $r=kt^2/n\to0$ and $B=\frac{k\sqrt t}{4n\sqrt{a(1-a)}}(1+Cr)$. Eventually,
--
--   $$\mathbb E_{H_\times}\varepsilon_{\rm worst}\le B,\qquad H_\times\{U:\varepsilon_{\rm worst}(U)>B\}\le e^{-cn}.$$
--
--   The error is reference-assisted, with one recovery for every input. For either excluded trivial case $k=0$ or $t=0$, the optimized error is exactly zero for every unitary encoder.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 11, Theorem 2, Eqs. (19)–(20): mean and typical worst-case error

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Theorem 2, PDF p.11, Eqs.(19)–(20): kt^2=o(n), with k outside sqrt(t). -/
theorem random_worst_error :
    AsymptoticGuarantee ChargeHaar true ∧ ZeroErrorGuarantee true := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
