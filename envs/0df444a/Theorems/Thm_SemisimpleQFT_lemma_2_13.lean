-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_2_13
-- name    : SemisimpleQFT.lemma_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:10:15.701168+00:00
-- url     : https://prove2.me/theorems/4b630ea7-6c55-4ef3-b69e-0b576958ee58
-- title:
--   Lemma 2.13: multiplication rule, index swap duality and left action of the Fourier basis
-- statement:
--   Let $A$ be a semisimple algebra with a chosen Fourier isomorphism and Fourier basis $E^\rho_{ij}$. Then:
--
--   1. (Matrix multiplication rule) $E^\rho_{ij}E^\sigma_{kl}=\delta_{\rho\sigma}\delta_{jk}E^\rho_{il}$.
--   2. (Index swap duality) $(E^\rho_{ji})^*=E^\rho_{ij}/d_\rho$ for the dual basis with respect to $\tau_{\mathbf L}$; explicitly $\tau_{\mathbf L}(E^\rho_{ij}E^\sigma_{kl})=d_\rho\,\delta_{\rho\sigma}\delta_{jk}\delta_{il}$.
--   3. (Left action invariance) $a\,E^\rho_{ij}=\sum_k\rho(a)_{ki}E^\rho_{kj}$ for every $a\in A$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 17, Lemma 2.13

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem lemma_2_13 {A : Type*} [Ring A] [Algebra ℂ A] {Λ J : Type*}
    [Fintype J] [DecidableEq J] (F : FourierData A Λ J) :
    (∀ i j k l : J, F.lab i = F.lab j → F.lab k = F.lab l →
      F.E i j * F.E k l = if j = k then F.E i l else 0) ∧
    (∀ i j k l : J, F.lab i = F.lab j → F.lab k = F.lab l →
      regTrace A (F.E i j * F.E k l) = if k = j ∧ l = i then (F.dim (F.lab i) : ℂ) else 0) ∧
    (∀ (a : A) (i j : J), F.lab i = F.lab j →
      a * F.E i j = ∑ k : J, F.rep a k i • F.E k j) := by sorry

end SemisimpleQFT
