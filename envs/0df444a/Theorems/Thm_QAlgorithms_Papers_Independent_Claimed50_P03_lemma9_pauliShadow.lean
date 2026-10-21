-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma9_pauliShadow
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma9_pauliShadow
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:54:35.853227+00:00
-- url     : https://prove2.me/theorems/e2111aaa-79dd-4914-baf8-cd4fecffa03d
-- title:
--   Lemma 9 (Shadow norm for Pauli observables [46])
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   For every phase-free $n$-qubit Pauli $P$,
--   $$\|P\|_{\rm sh}=3^{|P|/2}.$$
--   This includes weight zero, for which the uncentered norm of the identity is one. It fixes the locality cost of Pauli predictions.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 32, Lemma 9 (Shadow norm for Pauli observables [46])

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 9, paper p.32, C3; original arXiv:2002.08953, Supplementary
Lemma 3, S50. The norm is uncentered, so the identity has norm one. -/
theorem lemma9_pauliShadow (n : ℕ) (P : (Fin n → Fin 4)) :
    localPauliShadowNorm (wordMatrix P) = Real.rpow 3 ((pauliWeight P : ℝ) / 2) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
