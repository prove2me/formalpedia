-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P58_tetrahedralAchievability
-- name    : QAlgorithms.Papers.Independent.Information100.P58.tetrahedralAchievability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:17:30.779253+00:00
-- url     : https://prove2.me/theorems/f2b18b52-20be-4ca5-acd9-201ca3f56260
-- title:
--   Achievable tetrahedral product-code performance
-- statement:
--   Let $0\le p\le1$ and label four equiprobable messages by $(x,y)\in\{0,1\}^2$. With the standard Pauli matrices $\sigma_j$, define $r_{xy}=((-1)^x,(-1)^y,(-1)^{x+y})/\sqrt3$ and $\tau_{xy}=(I+\sum_jr_{xy,j}\sigma_j)/2$. The four input codewords are the density matrices $|x\rangle\langle x|\otimes|y\rangle\langle y|\otimes|x\oplus y\rangle\langle x\oplus y|\otimes\tau_{xy}$. A collective decoder exists for which every individual-message success is
--
--   $$P_{\rm tet}(p)=s_{4,2,p}(4)-\frac{3-\sqrt6}{2}p^2(1-p)^2,$$
--
--   where $s_{4,2,p}(4)=\sum_{k=0}^4\binom4k(1-p)^kp^{4-k}\min\{1,2^k/4\}$. This is an explicit achievable performance, without an assertion that it is the quantum optimum.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, PDF p. 27, Proposition 7.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Proposition 7.1, PDF pp.27–28: the explicitly defined tetrahedral product code has equal individual success. -/
theorem tetrahedralAchievability (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) :
    (∀ m, IsDensityMatrix (tetrahedralInput m)) ∧
    ∃ D : Fin 4 → Operator (Output 4 2), IsPOVM D ∧
      ∀ m, effectProb (D m) (erasure 4 2 p (tetrahedralInput m)) = tetrahedralValue p := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P58
