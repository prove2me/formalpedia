-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P66_twoSidedFactorizedAncilla
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P66.twoSidedFactorizedAncilla
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:47:45.884796+00:00
-- url     : https://prove2.me/theorems/d5f5c1a8-957d-4d87-b61a-320cca8a9925
-- title:
--   Equality of one-shot reconstruction expectations
-- statement:
--   Let $\mathcal E$ be any CPTP channel on $n\ge1$ qubits. Use the same named uniform frame on reference and output: global Clifford, product single-qubit Clifford, Pauli-6, or a fixed partition into smaller Clifford blocks. Choices on the two registers are independent. Write $Q_{u,b}=U_u^\dagger|b\rangle\langle b|U_u$ and let $\mathcal M^{-1}$ be the actual complex-linear inverse measurement channel. With $\rho_{\Lambda}=2^{-n}\Lambda_{\mathcal E}$, define
--
--   $$
--   \rho_a=\mathbb E_{u,v}\sum_{b,c}\operatorname{Tr}[\rho_{\Lambda}(Q_{u,b}\otimes Q_{v,c})]
--    \mathcal M^{-1}(Q_{u,b})\otimes\mathcal M^{-1}(Q_{v,c}),
--   $$
--
--   $$
--   \rho_t=\mathbb E_{u,v}\sum_c\operatorname{Tr}[\mathcal E(Q_{u,0})Q_{v,c}]
--    \mathcal M^{-1}(Q_{u,0}^{T})\otimes\mathcal M^{-1}(Q_{v,c}).
--   $$
--
--   For Pauli-6, the preparation-frame relabeling bit lets fixed outcome zero prepare each of the six eigenstates uniformly. Then
--
--   $$
--   \rho_t=\rho_a.
--   $$
--
--   This equality concerns reconstruction expectations for one fresh repetition per choice. It does not identify individual random snapshots, empirical matrices, or repeated-circuit experiments. Pauli-$Y$ transposition is an ensemble permutation exchanging the two eigenprojectors.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, PDF p. 15, Appendix B, B1-B4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Appendix B, PDF pp.14-15, B1-B4: equality of expectation matrices for
one fresh repetition with independent choices on the two registers. The
printed Pauli-Y pointwise transpose equality is replaced by an ensemble
outcome permutation. No empirical-data equality is asserted. -/
theorem twoSidedFactorizedAncilla (n : ℕ) (hn : 0 < n) (F : BasisChoiceFrame n)
    (hF : PaperFrame F) (E : Superop (Qubits n) (Qubits n)) (hE : IsChannel E) :
    twoSidedReconstruction F E = ancillaReconstruction F E := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P66

end
