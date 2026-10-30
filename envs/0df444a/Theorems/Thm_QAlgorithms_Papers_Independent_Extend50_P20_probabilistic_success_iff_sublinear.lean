-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_probabilistic_success_iff_sublinear
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.probabilistic_success_iff_sublinear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:11:33.765197+00:00
-- url     : https://prove2.me/theorems/f3859607-0fc1-42c9-b0a1-d82997dcf0fa
-- title:
--   Sharp asymptotic teleported-system rate
-- statement:
--   Fix $d\ge2$. Let $k:\mathbb N\to\mathbb N$ satisfy $1\le k(N)\le N$ for every $N\ge1$. Let $p_{\mathrm{opt}}(d,N,k(N))$ be the optimal exact MPBT success probability, optimizing both normalized resource and measurements. Then
--
--   $$p_{\mathrm{opt}}(d,N,k(N))\longrightarrow1\quad\Longleftrightarrow\quad\frac{k(N)}N\longrightarrow0.$$
--
--   Sublinear growth is therefore both necessary and sufficient for asymptotically certain optimal success. The converse excludes $d=1$, where success equals one for every valid system count. Equation (103) pins the source's sharp-rate claim; the dimension is fixed.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 14, Section 8 / sharp rate (also p.3 and Eq. (103) p.22)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Sharp rate claimed on PDF pp.3,14, pinned by Appendix C p.22, Eq.(103).
The converse requires d>=2: at d=1 the product is empty and success is always one. -/
theorem probabilistic_success_iff_sublinear (d : ℕ) (hd : 2 ≤ d) (k : ℕ → ℕ)
    (hk : ∀ N, 1 ≤ N → 1 ≤ k N ∧ k N ≤ N) :
    Tendsto (fun N => optimalMpbtSuccess d N (k N)) atTop (nhds 1) ↔
      Tendsto (fun N : ℕ => (k N : ℝ)/(N : ℝ)) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
