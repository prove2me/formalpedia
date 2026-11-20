-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_5_4
-- name    : SemisimpleQFT.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:57:52.408672+00:00
-- url     : https://prove2.me/theorems/292ec1eb-a5c2-4019-a302-cc970bd9649b
-- title:
--   Lemma 5.4: norms of Fourier states under a multiplicity-free restriction
-- statement:
--   Let $B\subseteq A$ be semisimple algebras with a $B$-adapted Fourier basis of $A$ and multiplicity-free branching, and assume $A$ is $\delta$-nice with respect to its computational basis. For $\sigma\in\widehat B$ and basis indices $k,l$ of $\sigma$, let $K$ be the number of irreps $\rho\in\widehat A$ with $\sigma\in\mathrm{Res}(\rho)^A_B$. Then
--   $$\|E^\sigma_{kl}\|_2^2=(1+(K-1)\varepsilon)\Big(\sum_{\rho:\ \sigma\in\mathrm{Res}(\rho)^A_B}\|E^\rho_{k\circ\rho,\,l\circ\rho}\|_2^2\Big)\quad\text{with }|\varepsilon|\le\delta,$$
--   i.e. $\big|\|E^\sigma_{kl}\|_2^2-\Sigma\big|\le(K-1)\,\delta\,\Sigma$ where $\Sigma$ is the sum on the right. The norm of $E^\sigma_{kl}$ is taken in the computational inner product of $A$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 33, Lemma 5.4, Eq. (5.13)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

open Classical in
theorem lemma_5_4 {R : Type*} [Ring R] [Algebra ℂ R] {A B : Subalgebra ℂ R} (hBA : B ≤ A)
    {ΛA ΛB : Type*} {JA JB : Type*} [Fintype JA] [DecidableEq JA] [Fintype JB] [DecidableEq JB]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (FA : FourierData A ΛA JA) (FB : FourierData B ΛB JB) (tr : JA → JB)
    (h : IsAdapted hBA FA FB tr) (c : CompBasis A ι) (δ : ℝ) (hδ : FA.IsNice c δ)
    (k l : JB) (hkl : FB.lab k = FB.lab l) :
    |c.norm (⟨((FB.E k l : B) : R), hBA (FB.E k l).2⟩ : A) ^ 2 -
        ∑ P : JA, ∑ Q : JA,
          if FA.lab P = FA.lab Q ∧ tr P = k ∧ tr Q = l then c.norm (FA.E P Q) ^ 2 else 0| ≤
      ((Nat.card {PQ : JA × JA // FA.lab PQ.1 = FA.lab PQ.2 ∧ tr PQ.1 = k ∧ tr PQ.2 = l} : ℝ) - 1) *
        δ * ∑ P : JA, ∑ Q : JA,
          if FA.lab P = FA.lab Q ∧ tr P = k ∧ tr Q = l then c.norm (FA.E P Q) ^ 2 else 0 := by sorry

end SemisimpleQFT
