-- Prove2me | Theorems.Thm_SemisimpleQFT_theorem_2_11
-- name    : SemisimpleQFT.theorem_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:08:57.694172+00:00
-- url     : https://prove2.me/theorems/579b0ac1-7c74-4abb-aaba-1b4319a8631e
-- title:
--   Theorem 2.11: the Fourier basis in terms of the dual basis
-- statement:
--   Let $A$ be a semisimple algebra with a chosen Fourier isomorphism $A\cong\bigoplus_\rho M_{d_\rho}(\mathbb{C})$ and Fourier basis $E^\rho_{ij}$, and let $\mathcal B(A)=\{a\}$ be any basis of $A$. Then a dual family $\{a^*\}$ of $\mathcal B(A)$ with respect to the left regular trace form $\tau_{\mathbf L}$ exists (i.e. $\tau_{\mathbf L}(a_i^*a_j)=\delta_{ij}$), and for every such dual family and all $\rho,i,j$,
--   $$E^\rho_{ij}=d_\rho\sum_{a\in\mathcal B(A)}\rho(a^*)_{ji}\,a .$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 16, Theorem 2.11, Eq. (2.7)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem theorem_2_11 {A : Type*} [Ring A] [Algebra ℂ A] {Λ J ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
    (F : FourierData A Λ J) (b : Module.Basis ι ℂ A) :
    (∃ bs : ι → A, IsRegDual b bs) ∧
    ∀ bs : ι → A, IsRegDual b bs → ∀ i j : J, F.lab i = F.lab j →
      F.E i j = (F.dim (F.lab i) : ℂ) • ∑ a : ι, F.rep (bs a) j i • b a := by sorry

end SemisimpleQFT
