-- Prove2me | Theorems.Thm_SystemicHoldings_FEfficient_F_rank_nullity
-- name    : SystemicHoldings.FEfficient.F_rank_nullity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:12.054632+00:00
-- url     : https://prove2.me/theorems/0d52cec5-c533-4dcf-8bf3-fdbb2910345b
-- title:
--   Proof of Theorem 4.1 b), EC p. 11 — rank(F) = 2K + N − 2 and null(F) = (N − 2)(K − 1)
-- statement:
--   Let $N\ge2$, $K\ge1$ and $v\in\mathbb R^N$ with $v_i\neq v_j$ for some $i,j$. Let $F\in\mathbb R^{(2K+N)\times KN}$ be the matrix of (EC.1.12), whose rows express $\mathbf 1_K^\top Q$, $Q\mathbf 1_N$ and $Qv$ in terms of $\mathrm{vec}(Q)$. Then
--   $$\mathrm{rank}(F) = 2K+N-2,\qquad \mathrm{null}(F) = KN-(2K+N-2) = (N-2)(K-1).$$
--
--   Combined with Remark EC.1.1, this gives the dimension of the affine set of f-efficient holding matrices, which is zero exactly when $N=2$ or $K=1$.
--
--   **Formalization Note** $\mathrm{null}(F)$ is the dimension (`Module.finrank`) of the kernel of the linear map $x\mapsto Fx$ on $\mathbb R^{K\times N}$. The natural-number subtractions are safe under $N\ge2$, $K\ge1$. Only the first half of Assumption 3 is assumed, as in the paper.
-- source:
--   Awiszus, Capponi & Weber, Market Efficient Portfolios in a Systemic Economy, arXiv:2003.10121v3, E-Companion p. 11 (PDF 41), proof of Theorem 4.1 b)

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model

namespace SystemicHoldings.FEfficient
open Matrix

theorem F_rank_nullity {K N : ℕ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (v : Fin N → ℝ) (hv : ∃ i j, v i ≠ v j) :
    (Fmat (K := K) v).rank = 2 * K + N - 2 ∧
    Module.finrank ℝ (LinearMap.ker (Fmat (K := K) v).mulVecLin) = (N - 2) * (K - 1) := by sorry

end SystemicHoldings.FEfficient
