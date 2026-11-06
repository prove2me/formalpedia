-- Prove2me | Theorems.Thm_SilverRateLB_lemma_3_5
-- name    : SilverRateLB.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:16.968431+00:00
-- url     : https://prove2.me/theorems/c5e9a383-721c-4c79-b226-1d89db75959e
-- title:
--   Lemma 3.5 — $[U_n(\Lambda)/c]^\nu\le a^\nu n+\Lambda^\nu$
-- statement:
--   Let $1<c\le2$, $p\in[p_{\mathrm{sil}}+c-1,\,3/2]$, $\nu=1/p$, and $a\ge2$. Then for every $n\ge0$ and $\Lambda\ge a$,
--   $$\Bigl[\frac{U_n(\Lambda)}{c}\Bigr]^\nu\le a^\nu n+\Lambda^\nu,\tag{17}$$
--   where $U_n(\Lambda)=\sup_{H\in[0,\infty)^n}V_\Lambda(H)$. Equivalently, $[V_\Lambda(H)/c]^\nu\le a^\nu n+\Lambda^\nu$ for every nonnegative schedule $H$ of length $n$.
--
--   With $\Lambda=an^p$ this gives $V_\Lambda(H)\le c\,2^pan^p$, the polynomial growth that (14) turns into the lower bound (19).
--
--   Differences from the source:
--   - generalization: a of Lemma 2.4 (tied to c through ε, γ) → any a ≥ 2, independent of c; reason: the argument uses only a ≥ 2; the paper's a satisfies it, so the statement specializes to the source's
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n → H : List ℝ with nonnegative entries, n = H.length; reason: same schedules
--   - encoding: [U_n(Λ)/c]^ν ≤ a^ν n + Λ^ν with U_n a supremum → (V a c Λ H / c)^(1/p) ≤ … for every nonnegative H of length n; reason: t ↦ (t/c)^ν is increasing on [0, ∞), so the bound on the supremum is equivalent to the bound for every H
-- source:
--   Ye, Liu, Silver Rate Is (Almost) Optimal for Gradient Descent, arXiv:2609.09152 (sha256 6797dde3…), Lemma 3.5, (17), p. 15; proof §B.3, p. 29

import Mathlib
import Definitions.Def_SilverRateLB_pSil
import Definitions.Def_SilverRateLB_V

namespace SilverRateLB

/-- **Lemma 3.5 (bound on `U_n`).** Let `1 < c ≤ 2`, `p ∈ [p_sil + c − 1, 3/2]` and `ν = 1/p`. Then,
for every `n ≥ 0` and `Λ ≥ a`, `[U_n(Λ)/c]^ν ≤ a^ν n + Λ^ν` (17).

Ye, Liu, *Silver Rate Is (Almost) Optimal for Gradient Descent*, arXiv:2609.09152, Lemma 3.5, (17), p. 15 (proof §B.3, p. 29).

**Formalization Note** `U_n(Λ) = sup_{H ∈ [0,∞)^n} V_Λ(H)` is not formed: the bound is stated for
every nonnegative `H` of length `n`, which is equivalent because `t ↦ (t/c)^ν` is increasing
on `[0, ∞)`. `a` is a parameter with `a ≥ 2` (the paper's satisfies it). -/
theorem lemma_3_5 (a c p : ℝ) (ha : 2 ≤ a) (hc1 : 1 < c) (hc2 : c ≤ 2)
    (hp1 : pSil + c - 1 ≤ p) (hp2 : p ≤ 3 / 2) (n : ℕ) (Λ : ℝ) (hΛ : a ≤ Λ) (H : List ℝ)
    (hlen : H.length = n) (hH : ∀ h ∈ H, 0 ≤ h) :
    (V a c Λ H / c) ^ (1 / p) ≤ a ^ (1 / p) * n + Λ ^ (1 / p) := by sorry

end SilverRateLB
