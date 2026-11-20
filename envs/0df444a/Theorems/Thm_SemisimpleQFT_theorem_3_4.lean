-- Prove2me | Theorems.Thm_SemisimpleQFT_theorem_3_4
-- name    : SemisimpleQFT.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:11:14.4661+00:00
-- url     : https://prove2.me/theorems/c4d5b16e-db71-4c45-97d3-13b8d1a60f93
-- title:
--   Theorem 3.4: $\|\mathrm{FT}_A-\widetilde{\mathrm{FT}}_A\|_\infty\le O(\delta\,|A|^{3/2})$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $A$ be a semisimple algebra with a chosen Fourier isomorphism and computational basis $\mathcal B(A)$, and let
--   $$\widetilde{\mathrm{FT}}_A|a\rangle=\sum_{\rho\in\widehat A}\sum_{i,j=1}^{d_\rho}\|E^\rho_{ij}\|_2\cdot\rho(a)_{ij}\,|\rho,i,j\rangle .$$
--   If $A$ is $\delta$-nice with $\delta\le1/2$ (the standing assumption of Section 3.1), then
--   $$\|\mathrm{FT}_A-\widetilde{\mathrm{FT}}_A\|_\infty\le C\,\delta\,|A|^{3/2},$$
--   where $|A|=\dim A$ and $\|\cdot\|_\infty$ is the operator norm.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, p. 20, Theorem 3.4, Eq. (3.19)

import Definitions.Def_SemisimpleQFT_Fourier

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem theorem_3_4 :
    ∃ C : ℝ, ∀ (A : Type) [Ring A] [Algebra ℂ A] (Λ J ι : Type)
      [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]
      (F : FourierData A Λ J) (b : Module.Basis ι ℂ A) (δ : ℝ),
      δ ≤ 1 / 2 → F.IsNice (CompBasis.ofBasis b) δ →
      QAlgorithms.specNorm (F.FT (CompBasis.ofBasis b) - F.FTtilde (CompBasis.ofBasis b)) ≤
        C * δ * (Fintype.card ι : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end SemisimpleQFT
