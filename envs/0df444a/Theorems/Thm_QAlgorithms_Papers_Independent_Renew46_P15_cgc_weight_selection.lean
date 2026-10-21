-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_cgc_weight_selection
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.cgc_weight_selection
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:14:58.837762+00:00
-- url     : https://prove2.me/theorems/f80e407f-8e19-4a92-b5cf-671d8b5bbadc
-- title:
--   CG coefficient z-weight selection rule
-- statement:
--   Fix an integer $N\ge2$ and two arbitrary finite-dimensional irreducible representations $S,S^\prime$ of $\mathrm{SU}(N)$, with normalized weakly decreasing integral top rows ending in zero. Use their orthonormal Gelfand–Tsetlin (GT) bases, without normalizing lower rows, and the real CG coefficients intertwining the common complexified Lie-algebra generators. These same coefficients apply to $\mathrm{SL}(N,\mathbb C)$.
--
--   Let $T$ be any occurring summand, let $\alpha$ distinguish any of its copies, and let $M,M^\prime,M^{\prime\prime}$ be valid GT basis labels in $S,S^\prime,T$, respectively. For a pattern $M$, write $\sigma_l(M)$ for its row sum, with $\sigma_0=0$, and define its z-weight by $\lambda_l(M)=\sigma_l(M)-(\sigma_{l+1}(M)+\sigma_{l-1}(M))/2$ for $1\le l<N$. Then
--
--   $$
--    W_z(M^{\prime\prime})\ne W_z(M)+W_z(M^\prime)
--    \quad\Longrightarrow\quad C_{M,M^\prime}^{M^{\prime\prime},\alpha}=0.
--   $$
--
--   This rule applies to every copy and only gives a necessary condition for a coefficient to be nonzero. Z-weights make the assertion invariant under determinant shifts of output labels.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 10, §IX, Eq.(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- IX, (34), PDF p.10: unequal z-weight sums force a zero coefficient,
for every output state and copy; the reverse implication is not asserted. -/
theorem cgc_weight_selection {n r : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t)
    (j : Fin r) (out : Pattern (t j)) (m : Pattern s) (mPrime : Pattern sPrime)
    (h : zWeight out ≠ zWeight m + zWeight mPrime) :
    c.coeff ⟨j, out⟩ (m, mPrime) = 0 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
