-- Prove2me | Theorems.Thm_SemisimpleQFT_corollary_2_12
-- name    : SemisimpleQFT.corollary_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:09:32.111254+00:00
-- url     : https://prove2.me/theorems/335dc84b-ef27-45ec-81bd-12749d5cc829
-- title:
--   Corollary 2.12: Schur orthogonality for the irreps of a semisimple algebra
-- statement:
--   Let $A$ be a semisimple algebra with a chosen Fourier isomorphism, $\mathcal B(A)$ a basis of $A$ and $\{a^*\}$ a dual family with respect to $\tau_{\mathbf L}$. For all irreps $\rho,\sigma$, all basis indices $i,j$ of $\rho$ and $k,l$ of $\sigma$,
--   $$d_\rho\sum_{a\in\mathcal B(A)}\rho(a^*)_{ji}\,\sigma(a)_{kl}=\delta_{\rho\sigma}\delta_{ik}\delta_{jl}.$$
--   (In the formal statement the indices of all irreps form one set, so $\delta_{\rho\sigma}\delta_{ik}\delta_{jl}$ is the condition $i=k$ and $j=l$.)
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 17, Corollary 2.12, Eq. (2.10)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem corollary_2_12 {A : Type*} [Ring A] [Algebra ℂ A] {Λ J ι : Type*}
    [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
    (F : FourierData A Λ J) (b : Module.Basis ι ℂ A) (bs : ι → A) (hbs : IsRegDual b bs)
    (i j k l : J) (hij : F.lab i = F.lab j) (hkl : F.lab k = F.lab l) :
    (F.dim (F.lab i) : ℂ) * ∑ a : ι, F.rep (bs a) j i * F.rep (b a) k l =
      if i = k ∧ j = l then 1 else 0 := by sorry

end SemisimpleQFT
