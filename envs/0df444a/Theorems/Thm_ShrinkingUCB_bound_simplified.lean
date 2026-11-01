-- Prove2me | Theorems.Thm_ShrinkingUCB_bound_simplified
-- name    : ShrinkingUCB.bound_simplified
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:27.297817+00:00
-- url     : https://prove2.me/theorems/cc9d5b9a-3dbb-4526-98a8-1bb9b97a30f4
-- title:
--   End of the last display, p.19 — the bound equals $K+\alpha(K+10\sqrt{dKT\log(KT)})$ and is $\tilde O(K\sqrt d+d\sqrt{KT})$
-- statement:
--   Let $d\ge1$, $1\le K\le N$, $T\ge1$, $\delta\in(0,1)$, $\alpha=\sqrt{d\ln((1+N+TN)/\delta)}+1$. Then
--
--   $$
--   K+\alpha K+10\alpha\sqrt{dKT\log(KT)}=K+\Big(\sqrt{d\ln\tfrac{1+N+TN}{\delta}}+1\Big)\Big(K+10\sqrt{dKT\log(KT)}\Big),
--   $$
--
--   and this quantity is at most
--
--   $$
--   20\,\sqrt{\ln\tfrac{1+N+TN}{\delta}}\,\sqrt{1+\log(KT)}\,\big(K\sqrt d+d\sqrt{KT}\big).
--   $$
--
--   This makes precise the claim $\tilde O(K\sqrt d+d\sqrt{KT})$ of Theorem 3: the two terms are the fixed cost and the variable cost.
--
--   Differences from the source:
--   - encoding: = Õ(K√d + d√(KT)) → ≤ 20 √(ln((1 + N + TN)/δ)) √(1 + log(KT)) (K√d + d√(KT)); reason: Õ(·) "hides logarithmic factors" (p.6); the factor is made explicit, and its constant 20 is not on the page
--   - reading: d, K, N, T unconstrained on the page and δ unstated → 1 ≤ d, 1 ≤ K ≤ N, 1 ≤ T, 0 < δ < 1; reason: "selects a set of K products from [N]" (p.9) needs K ≤ N; ln δ needs δ > 0; for δ ≥ 1 the claim is empty
--   - reading: log(KT) → Real.log, the natural logarithm; reason: §4 writes ln throughout, and the log of Lemma 2 comes from Chu et al. (2011), whose logarithm is natural; the base changes the bound, so this is a reading, not an encoding
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, End of the last display of the proof of Theorem 3, p.19

import Definitions.Def_ShrinkingUCB_alpha

namespace ShrinkingUCB

/-- The end of the last display of the proof of Theorem 3, p.19 of arXiv:1903.07844v2:
`K + αK + 10α√(dKT log(KT)) = K + (√(d ln((1 + N + TN)/δ)) + 1)(K + 10√(dKT log(KT)))`, and this
is `Õ(K√d + d√(KT))`, in the explicit form
`≤ 20 √(ln((1 + N + TN)/δ)) √(1 + log(KT)) (K√d + d√(KT))`. -/
theorem bound_simplified {d N : ℕ} (K T : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (hKN : K ≤ N) (hT : 1 ≤ T)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (K : ℝ) + alpha d N T δ * K
        + 10 * alpha d N T δ * √((d : ℝ) * K * T * Real.log ((K : ℝ) * T)) =
      K + (√((d : ℝ) * Real.log ((1 + (N : ℝ) + (T : ℝ) * (N : ℝ)) / δ)) + 1)
        * (K + 10 * √((d : ℝ) * K * T * Real.log ((K : ℝ) * T))) ∧
    (K : ℝ) + alpha d N T δ * K
        + 10 * alpha d N T δ * √((d : ℝ) * K * T * Real.log ((K : ℝ) * T)) ≤
      20 * (√(Real.log ((1 + (N : ℝ) + (T : ℝ) * (N : ℝ)) / δ))
          * √(1 + Real.log ((K : ℝ) * T)))
        * ((K : ℝ) * √(d : ℝ) + (d : ℝ) * √((K : ℝ) * T)) := by sorry

end ShrinkingUCB
