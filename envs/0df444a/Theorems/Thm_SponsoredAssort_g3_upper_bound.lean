-- Prove2me | Theorems.Thm_SponsoredAssort_g3_upper_bound
-- name    : SponsoredAssort.g3_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:53.943008+00:00
-- url     : https://prove2.me/theorems/1ae51c58-3863-42dc-95fe-4b883d0ba2b2
-- title:
--   Appendix G.3, OA p.38 — every IC mechanism has $\inf_v R(m,v)/R(m^{FB},v)\le1/n$ (corrected: $1/n+\eta$)
-- statement:
--   Let $r>0$ with $r_i/r_{i+1}\ge n$ for all $i$, and let $m$ be an incentive compatible mechanism. For every $\eta>0$ there is a profile $v\ne0$ with
--
--   $$
--   \frac{R(m,v)}{R(m^{FB},v)}\ \le\ \frac1n+\eta .
--   $$
--
--   Hence $\inf_{v\ne0}R(m,v)/R(m^{FB},v)\le1/n$, which with (Prior independent) gives $\gamma^{PI}(r)\le1/n$.
--
--   Differences from the source:
--   - correction: there exists $v$ with $R(m,v)/R(m^{FB},v)\le1/n$ → for every $\eta>0$ there is $v\ne0$ with ratio $\le1/n+\eta$; reason: false as printed: for $n=2$, $r=(2,1)$ and $m=m^{\downarrow}$ (IC), every $v\ne0$ has ratio $>1/2$; the proof itself ends with $1/n+o(1)$
--   - encoding: $v\in\mathbb R^n_+$ → $v\ne0$; reason: the ratio is $0/0$ at $v=0$
--   - encoding: $r_i/r_{i+1}\ge n$, sellers $1,\dots,n$ → $n\,r_{i+1}\le r_i$, sellers `Fin n`; reason: 0-based indexing; equivalent for $r>0$
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix G.3, proof of Proposition 5.4, OA pp.38–39

import Mathlib
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_firstBest

open scoped NNReal

namespace SponsoredAssort

/-- **Appendix G.3, opening claim** (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), proof of
Proposition 5.4, OA pp.38–39), corrected. Let `r > 0` with `rᵢ/rᵢ₊₁ ≥ n` for all `i`. For every
incentive compatible mechanism `m` and every `η > 0` there is a profile `v ≠ 0` with
`R(m, v) / R(m^FB, v) ≤ 1/n + η`; that is, `inf_{v ≠ 0} R(m, v)/R(m^FB, v) ≤ 1/n`.

**Formalization Note.** The printed claim "there exists `v` such that `R(m, v)/R(m^FB, v) ≤ 1/n`"
is false: for `n = 2`, `r = (2, 1)` and `m = m↓` (IC by Corollary 5.3), every `v ≠ 0` has ratio
strictly above `1/2`. The proof gives `1/n + o(1)`, which is what the infimum needs; the statement
carries the tolerance `η`. `v ≠ 0` excludes the `0/0` point. Sellers are 0-based, and
`rᵢ/rᵢ₊₁ ≥ n` is written `n·rᵢ₊₁ ≤ rᵢ`. -/
theorem g3_upper_bound {n : ℕ} [NeZero n] (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hratio : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → (n : ℝ) * r j ≤ r i)
    (m : Mechanism n) (hIC : IsIC r m) :
    ∀ η : ℝ, 0 < η → ∃ v : Attr n, v ≠ 0 ∧
      welfare r (m.alloc v) v ≤ (1 / (n : ℝ) + η) * firstBest r v := by sorry

end SponsoredAssort
