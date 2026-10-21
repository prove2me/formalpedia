-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma11_shadowNorm
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma11_shadowNorm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:56:04.707979+00:00
-- url     : https://prove2.me/theorems/0826396b-45fe-4717-bddb-37e7752fdda3
-- title:
--   Lemma 11 (Shadow norm for bounded-degree observables)
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   For integers $k,d\ge1$, set
--   $$C(k,d)=\frac{\sqrt{2k!}}{\sqrt d\,k^{k+5/2}(2\sqrt6+4\sqrt3)^k}.$$
--   A bounded-degree decomposition means a finite sum of Hermitian terms supported on at most $k$ wires each, with at most $d$ terms incident on any wire.
--
--   For fixed $k,d\ge1$, uniformly for every $n\ge1$ and Hermitian $O$ with such a bounded-degree decomposition,
--   $$\|O\|_{\rm sh}\le3^{k/2}\frac3{C(k,d)}\|O\|.$$
--   The explicitly sufficient constant is independent of the register size and of the observable.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 33, Lemma 11 (Shadow norm for bounded-degree observables)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Lemma 11, paper p.33, C8, with the explicit sufficient constant
3^(k/2) times 3/C(k,d) from C5 and B12, uniform in n and O. -/
theorem lemma11_shadowNorm (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    ∀ (n : ℕ), 1 ≤ n → ∀ O : (Matrix (Qubits n) (Qubits n) ℂ), O.IsHermitian →
      HasBoundedDegree k d O →
      localPauliShadowNorm O ≤ Real.rpow 3 ((k : ℝ) / 2) * (3 / degreeConstant k d) * specNorm O := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
