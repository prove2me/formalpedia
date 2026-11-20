-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_5_3
-- name    : SemisimpleQFT.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:16:53.567717+00:00
-- url     : https://prove2.me/theorems/a0c4fd3e-8ac3-45cc-b85f-7387fd2984b3
-- title:
--   Lemma 5.3: Fourier states of a subalgebra in the adapted Fourier basis
-- statement:
--   Let $B\subseteq A$ be semisimple algebras and assume the Fourier basis of $A$ is given with respect to a $B$-adapted basis with a multiplicity-free branching rule (Eqs. (5.7)–(5.8)). For any irrep $\sigma\in\widehat B$ and basis indices $k,l$ of $\sigma$,
--   $$E^\sigma_{kl}=\sum_{\rho:\ \sigma\in\mathrm{Res}(\rho)^A_B}E^\rho_{k\circ\rho,\;l\circ\rho},$$
--   where $E^\sigma_{kl}$, a Fourier basis element of $B$, is regarded as an element of $A$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 32, Lemma 5.3, Eq. (5.9)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

open Classical in
theorem lemma_5_3 {R : Type*} [Ring R] [Algebra ℂ R] {A B : Subalgebra ℂ R} (hBA : B ≤ A)
    {ΛA ΛB : Type*} {JA JB : Type*} [Fintype JA] [DecidableEq JA] [Fintype JB] [DecidableEq JB]
    (FA : FourierData A ΛA JA) (FB : FourierData B ΛB JB) (tr : JA → JB)
    (h : IsAdapted hBA FA FB tr) (k l : JB) (hkl : FB.lab k = FB.lab l) :
    ((FB.E k l : B) : R) =
      ∑ P : JA, ∑ Q : JA,
        if FA.lab P = FA.lab Q ∧ tr P = k ∧ tr Q = l then ((FA.E P Q : A) : R) else 0 := by sorry

end SemisimpleQFT
