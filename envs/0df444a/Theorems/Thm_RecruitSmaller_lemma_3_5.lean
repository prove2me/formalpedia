-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_5
-- name    : RecruitSmaller.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:06.812436+00:00
-- url     : https://prove2.me/theorems/4d1a0e24-1fa3-44fd-916d-02e247642eaf
-- title:
--   Lemma 3.5 — $\Pr[s^{(i)}_{n+2}\le x]-\Pr[s^{(i)}_n\le x]=p^iA_{n,i}(p)$
-- statement:
--   For any $n\ge i\ge1$ and threshold $x\in\mathbb R$, with seller costs i.i.d. with CDF $F_S$ and $p:=F_S(x)\in[0,1]$,
--   $$
--   \Pr_{s_{n+2}}\bigl[s^{(i)}_{n+2}\le x\bigr]-\Pr_{s_n}\bigl[s^{(i)}_n\le x\bigr]=p^iA_{n,i}(p), \tag{3.8}
--   $$
--   where $A_{n,i}(p)=\binom{n}{i-1}(1-p)^{n-i+1}(2-p)+\binom{n}{i-2}(1-p)^{n-i+2}$ with $\binom{n}{-1}=0$.
--
--   This is the exact recruitment gain at rank $i$: how much two extra sellers raise the probability that the $i$-th cheapest cost is below $x$.
--
--   Differences from the source:
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.5, p.13, eq. (3.8); proof p.25

import Mathlib
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_A

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller

/-- **Lemma 3.5** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.13, eq. (3.8); proof p.25): for any `n ≥ i ≥ 1` and
threshold `x ∈ ℝ` with `p := F_S(x) ∈ [0, 1]`,
`Pr_{s_{n+2}}[s⁽ⁱ⁾_{n+2} ≤ x] − Pr_{sₙ}[s⁽ⁱ⁾ₙ ≤ x] = pⁱ A_{n,i}(p)`.

**Formalization Note** `F_S = cdf μS`; the seller profiles are i.i.d. from `μS` (product laws). -/
theorem lemma_3_5 (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (μS : Measure ℝ) [IsProbabilityMeasure μS] (x : ℝ) :
    ((Measure.pi fun _ : Fin (n + 2) => μS) {s | sellerOrd s i ≤ x}).toReal -
        ((Measure.pi fun _ : Fin n => μS) {s | sellerOrd s i ≤ x}).toReal =
      (cdf μS x) ^ i * A n i (cdf μS x) := by sorry

end RecruitSmaller
