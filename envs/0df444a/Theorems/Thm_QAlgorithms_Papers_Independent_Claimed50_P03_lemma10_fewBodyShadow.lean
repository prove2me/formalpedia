-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma10_fewBodyShadow
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma10_fewBodyShadow
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:55:27.796095+00:00
-- url     : https://prove2.me/theorems/e755ffdd-a8e5-4ea6-96cb-11d1ef93d5c2
-- title:
--   Lemma 10 (Shadow norm for few-body observables [46])
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   Let $O$ be Hermitian and supported on one set $S$ of at most $k$ wires; equivalently all nonzero Pauli coefficients have support contained in $S$. Then
--   $$\|O\|_{\rm sh}\le2^k\|O\|.$$
--   This few-body support condition is distinct from being a sum of many local terms. The bound includes scalar observables and empty support.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 32, Lemma 10 (Shadow norm for few-body observables [46])

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 10, paper p.32, C4; original arXiv:2002.08953, Supplementary
Proposition 3, S51. O is supported on one set of at most k wires,
as distinct from an arbitrary sum of many k-body terms. -/
theorem lemma10_fewBodyShadow (n k : ℕ) (O : (Matrix (Qubits n) (Qubits n) ℂ)) (hO : O.IsHermitian)
    (S : Finset (Fin n)) (hcard : S.card ≤ k)
    (hsupport : ∀ P : (Fin n → Fin 4), ¬ wordSupport P ⊆ S → coefficient O P = 0) :
    localPauliShadowNorm O ≤ (2 : ℝ) ^ k * specNorm O := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
