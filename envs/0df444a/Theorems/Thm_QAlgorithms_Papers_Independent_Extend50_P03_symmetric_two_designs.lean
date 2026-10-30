-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P03_symmetric_two_designs
-- name    : QAlgorithms.Papers.Independent.Extend50.P03.symmetric_two_designs
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:58:40.449641+00:00
-- url     : https://prove2.me/theorems/dbf8fcc6-9808-402f-8cf1-cabfe1d4b35f
-- title:
--   §6: extension to exact charge-conserving 2-designs
-- statement:
--   A code encodes $k$ logical qubits in $n$ physical qubits, with $0\le k\le n$, by appending a fixed normalized $(n-k)$-qubit eigenvector $\psi_\alpha$ of the Hamming-weight charge $Q^{(n-k)}$ with eigenvalue $0\le\alpha\le n-k$, then applying $U$. Thus $\mathcal E_U(\rho)=U(\rho\otimes|\psi_\alpha\rangle\langle\psi_\alpha|)U^\dagger$. The ancilla is chosen independently of $U$. The law $H_\times$ is probability Haar on the full charge centralizer, including every sector phase. Erasure of a set $S$ of $t\le n$ wires gives its complement to the decoder. Fidelity $F$ means root fidelity and $P=\sqrt{1-F^2}$. The optimized Choi error uses normalized $k$ EPR pairs; the optimized worst error chooses one CPTP decoder before all normalized joint logical/reference states over every finite reference dimension. Replace $H_\times$ by any probability ensemble supported on the full charge centralizer whose full $(1,1)$ and $(2,2)$ unitary twirls agree with $H_\times$, including cross-sector phases and correlations. Then the preceding expectation and failure estimates remain valid:
--
--   $$\text{Theorem 1, Theorem 2, Lemma 2, and their simultaneous flagged-erasure bounds hold.}$$
--
--   The two main bounds keep their separate growth regimes, constants uniform over the matching ensembles; Lemma 2 keeps its compact-interior/small-erasure assumptions. This exact-design statement supplies neither an approximate-design error term nor an efficient circuit construction.
-- source:
--   Charge-conserving unitaries typically generate optimal covariant quantum error-correcting codes, arXiv:2102.11835v1, PDF p. 14, §6: extension to exact charge-conserving 2-designs

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

/-- Section 6, PDF pp.14–15: the bounds extend to exact full centralizer 2-designs.
No approximate-design rate or efficient circuit construction is asserted. -/
theorem symmetric_two_designs :
    AsymptoticGuarantee ExactDesign false ∧ AsymptoticGuarantee ExactDesign true ∧
    ConcentrationGuarantee ExactDesign ∧ PatternGuarantee ExactDesign := by sorry

end QAlgorithms.Papers.Independent.Extend50.P03

end
