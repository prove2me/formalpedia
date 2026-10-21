-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_highestWeight_kernel_dimension
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.highestWeight_kernel_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:15:38.284356+00:00
-- url     : https://prove2.me/theorems/3599c3bb-965e-42c5-af61-582bbb2be2c3
-- title:
--   Highest-weight system kernel dimension
-- statement:
--   Fix an integer $N\ge2$ and two arbitrary finite-dimensional irreducible representations $S,S^\prime$ of $\mathrm{SU}(N)$, with normalized weakly decreasing integral top rows ending in zero. Use their orthonormal Gelfand–Tsetlin (GT) bases, without normalizing lower rows, and the real CG coefficients intertwining the common complexified Lie-algebra generators. These same coefficients apply to $\mathrm{SL}(N,\mathbb C)$.
--
--   Let $T$ be an occurring output irrep, and let $V_{W_z(H_T)}$ be the real coefficient space spanned by product basis labels with z-weight equal to that of its highest state $H_T$. For $1\le l<N$, let $J_{+,\mathrm{prod}}^{(l)}=J_{+,S}^{(l)}\otimes I+I\otimes J_{+,S^\prime}^{(l)}$. The homogeneous highest-state equations have solution space
--
--   $$
--    K_T=V_{W_z(H_T)}\cap\bigcap_{l=1}^{N-1}\ker J_{+,\mathrm{prod}}^{(l)},
--    \qquad \dim_{\mathbb R}K_T=N_{S,S^\prime}^{T}.
--   $$
--
--   Thus each outer-multiplicity copy contributes one independent highest-state coefficient vector. Since the matrices are real, complexification gives the corresponding complex solution-space dimension as well. Restriction to the target weight is essential.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 10, §X, Eqs.(35)–(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- X, (35)-(36), PDF p.10: the restricted highest-weight kernel has dimension
exactly the outer multiplicity, rather than counting other highest weights. -/
theorem highestWeight_kernel_dimension {n r : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t) (j : Fin r) :
    Module.finrank ℝ (highestKernel s sPrime (t j)) =
      outerMultiplicity t (t j) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
