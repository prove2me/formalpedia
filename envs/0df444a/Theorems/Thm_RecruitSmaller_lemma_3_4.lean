-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_4
-- name    : RecruitSmaller.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:10:51.280647+00:00
-- url     : https://prove2.me/theorems/8663bda8-abaa-4240-8a6e-ac6c422f81dc
-- title:
--   Lemma 3.4 — evaluation of $\Delta_{n,k,i}(x,b^{(i)})$ when $b^{(i)}\ge x$
-- statement:
--   Let $m\ge n\ge i\ge1$, $k\ge n+1$ and $x\in\mathbb R$, let seller costs be i.i.d. with CDF $F_S$, and set $p:=F_S(x)$ and $q:=F_S(b^{(i)})$. When $b^{(i)}\ge x$,
--   $$
--   \Delta_{n,k,i}(x,b^{(i)})=\Bigl(\Pr_{s_k}\bigl[s^{(i)}_k\le x\bigr]-\Pr_{s_n}\bigl[s^{(i)}_n\le x\bigr]\Bigr)-\binom{k}{i}p^i(1-q)^{k-i}. \tag{3.7}
--   $$
--   The subtracted term is the probability that exactly $i$ of the $k$ sellers cost at most $x$ and the other $k-i$ cost more than $b^{(i)}$: the trade-reduction loss at rank $i$.
--
--   **Formalization Note** The value of $b^{(i)}$ is a real $y\ge x$; $\Delta$ depends on $b^{(i)}$ only through it. The number of buyers $m$ and the hypothesis $n\le m$ are kept as printed.
--
--   Differences from the source:
--   - encoding: b⁽ⁱ⁾ with b⁽ⁱ⁾ ≥ x → an arbitrary real y with x ≤ y, q = F_S(y); reason: Δ_{n,k,i}(x, b⁽ⁱ⁾) depends on b⁽ⁱ⁾ only through its value; every value of b⁽ⁱ⁾ is such a y
--   - encoding: distributions with CDFs F_B, F_S on ℝ → probability measures μB, μS on ℝ with F_B = cdf μB, F_S = cdf μS; reason: every CDF on ℝ is the CDF of exactly one probability measure; same instances
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.4, p.13, eq. (3.7); proof p.24

import Mathlib
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_Delta

open MeasureTheory ProbabilityTheory

namespace RecruitSmaller

/-- **Lemma 3.4** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.13, eq. (3.7); proof p.24): let `m ≥ n ≥ i ≥ 1`,
`k ≥ n + 1` and `x ∈ ℝ`, and set `p := F_S(x)`, `q := F_S(b⁽ⁱ⁾)`. When `b⁽ⁱ⁾ ≥ x`,
`Δ_{n,k,i}(x, b⁽ⁱ⁾) = (Pr_{sₖ}[s⁽ⁱ⁾ₖ ≤ x] − Pr_{sₙ}[s⁽ⁱ⁾ₙ ≤ x]) − C(k, i) pⁱ (1 − q)^{k−i}`.

**Formalization Note** `y` stands for the value of `b⁽ⁱ⁾`; `Δ` depends on `b⁽ⁱ⁾` only through it.
`F_S = cdf μS`. The number of buyers `m` and `n ≤ m` are kept as on the page, though `Δ` does not
involve buyers. -/
theorem lemma_3_4 (m n i k : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hnm : n ≤ m) (hk : n + 1 ≤ k)
    (μS : Measure ℝ) [IsProbabilityMeasure μS] (x y : ℝ) (hxy : x ≤ y) :
    Delta μS n k i x y =
      (((Measure.pi fun _ : Fin k => μS) {s | sellerOrd s i ≤ x}).toReal -
          ((Measure.pi fun _ : Fin n => μS) {s | sellerOrd s i ≤ x}).toReal) -
        (k.choose i : ℝ) * (cdf μS x) ^ i * (1 - cdf μS y) ^ (k - i) := by sorry

end RecruitSmaller
