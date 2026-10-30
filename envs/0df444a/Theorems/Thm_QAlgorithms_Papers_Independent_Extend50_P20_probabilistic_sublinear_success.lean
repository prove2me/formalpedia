-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_probabilistic_sublinear_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.probabilistic_sublinear_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:06:00.148814+00:00
-- url     : https://prove2.me/theorems/d9db1184-8ae7-45fd-ad21-2daac348bbe2
-- title:
--   Sublinear teleportation has asymptotically certain success
-- statement:
--   Fix an integer $d\ge1$. Let $k:\mathbb N\to\mathbb N$ satisfy $1\le k(N)\le N$ for every $N\ge1$. Let $p_{\mathrm{opt}}(d,N,k(N))$ denote the optimal exact MPBT success probability, optimizing both the normalized resource and measurement in the ordered-port protocol. If $k(N)/N\to0$ in the real numbers, then
--
--   $$\lim_{N\to\infty}p_{\mathrm{opt}}(d,N,k(N))=1.$$
--
--   The teleported system count may therefore grow with the resource size. **Formalization Note** The total sequence's value at $N=0$ has no effect on this limit.
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 11, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Theorem 4, PDF p.11; Appendix C p.22, Eqs.(100)-(104).
Dimension d is fixed and k(N)/N is real division. N=0 is irrelevant to the limit. -/
theorem probabilistic_sublinear_success (d : ℕ) (hd : 0 < d) (k : ℕ → ℕ)
    (hk : ∀ N, 1 ≤ N → 1 ≤ k N ∧ k N ≤ N)
    (ho : Tendsto (fun N : ℕ => (k N : ℝ)/(N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N => optimalMpbtSuccess d N (k N)) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
