-- Prove2me | Theorems.Thm_SilverRateLB_lemma_B_2
-- name    : SilverRateLB.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:29.367759+00:00
-- url     : https://prove2.me/theorems/86cb6e6b-f1db-4365-9048-f9f443aa4161
-- title:
--   Lemma B.2 — the scalar inequality $W^\nu\le x^\nu+y^\nu$
-- statement:
--   Let $1<c\le2$, $p\in[p_{\mathrm{sil}}+c-1,\,3/2]$ and $\nu=1/p$, and let $a\ge2$. If $x,y\ge a$ and $B>0$ satisfy (16),
--   $$W=x+y+B-(a-2),\qquad WB=cxy,$$
--   then
--   $$W^\nu\le x^\nu+y^\nu.$$
--
--   It is the inductive step of Lemma 3.5: combining two subproblems multiplies the cost by at most the factor dictated by the exponent $p$.
--
--   Differences from the source:
--   - generalization: a of Lemma 2.4 (tied to c through ε, γ) → any a ≥ 2, independent of c; reason: the argument uses only a ≥ 2; the paper's a satisfies it, so the statement specializes to the source's
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma B.2, p. 28

import Mathlib
import Definitions.Def_SilverRateLB_pSil

namespace SilverRateLB

/-- **Lemma B.2 (the scalar inequality).** Let `1 < c ≤ 2`, `p ∈ [p_sil + c − 1, 3/2]` and
`ν = 1/p`. If `x, y ≥ a` and `B > 0` satisfy (16), i.e. `W = x + y + B − (a − 2)` and
`W B = c x y`, then `W^ν ≤ x^ν + y^ν`.

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma B.2, p. 28.

**Formalization Note** `a` is a parameter with `a ≥ 2` (the paper's `a` of Lemma 2.4 satisfies
it); `ν` is written `1 / p` and powers are `Real.rpow` of positive numbers. -/
theorem lemma_B_2 (a c p : ℝ) (ha : 2 ≤ a) (hc1 : 1 < c) (hc2 : c ≤ 2)
    (hp1 : pSil + c - 1 ≤ p) (hp2 : p ≤ 3 / 2) (x y B W : ℝ) (hx : a ≤ x) (hy : a ≤ y)
    (hB : 0 < B) (hW : W = x + y + B - (a - 2)) (hWB : W * B = c * x * y) :
    W ^ (1 / p) ≤ x ^ (1 / p) + y ^ (1 / p) := by sorry

end SilverRateLB
