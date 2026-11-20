-- Prove2me | Theorems.Thm_SemisimpleQFT_lemma_3_5
-- name    : SemisimpleQFT.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:10:47.420554+00:00
-- url     : https://prove2.me/theorems/970111ef-233d-411a-aac9-b62123a26541
-- title:
--   Lemma 3.5: irrep matrix elements of a $\delta$-nice algebra
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $A$ be a semisimple algebra with a chosen Fourier isomorphism, $\mathcal B(A)$ a basis with dual family $\{a^*\}$ with respect to $\tau_{\mathbf L}$, and suppose $A$ is $\delta$-nice with respect to $\mathcal B(A)$ with $\delta\le 1/2$. Then for every basis element $a\in\mathcal B(A)$ and all $\rho,i,j$,
--   $$\left|\rho(a)_{ij}-\frac{d_\rho\,\overline{\rho(a^*)_{ji}}}{\|E^\rho_{ij}\|_2^2}\right|\le\frac{C\,\delta\,\sqrt{|A|}}{\|E^\rho_{ij}\|_2}.$$
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 20, Lemma 3.5, Eq. (3.20)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem lemma_3_5 :
    ∃ C : ℝ, ∀ (A : Type) [Ring A] [Algebra ℂ A] (Λ J ι : Type)
      [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
      (F : FourierData A Λ J) (b : Module.Basis ι ℂ A) (bs : ι → A) (δ : ℝ),
      IsRegDual b bs → δ ≤ 1 / 2 → F.IsNice (CompBasis.ofBasis b) δ →
      ∀ (a : ι) (i j : J), F.lab i = F.lab j →
        ‖F.rep (b a) i j -
            (F.dim (F.lab i) : ℂ) * conj (F.rep (bs a) j i) /
              (((CompBasis.ofBasis b).norm (F.E i j) : ℝ) : ℂ) ^ 2‖ ≤
          C * δ * Real.sqrt (Fintype.card ι : ℝ) / (CompBasis.ofBasis b).norm (F.E i j) := by sorry

end SemisimpleQFT
