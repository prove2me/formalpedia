-- Prove2me | Theorems.Thm_RecruitSmaller_lemma_3_2
-- name    : RecruitSmaller.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:40.959275+00:00
-- url     : https://prove2.me/theorems/a465de8c-f176-4d59-a157-549125aa44a1
-- title:
--   Lemma 3.2 — $\mathrm{STR}(b,s_k)\ge\sum_{i=1}^n(b^{(i)}-s^{(i)}_k)\mathbb 1[b^{(i)}\ge s^{(i+1)}_k]$
-- statement:
--   For any $m\ge n\ge1$, any $k\ge n+1$ and any realization $(b,s_k)\in\mathbb R^m\times\mathbb R^k$,
--   $$
--   \mathrm{STR}(b,s_k)\ \ge\ \sum_{i=1}^{n}\bigl(b^{(i)}-s^{(i)}_k\bigr)\,\mathbb 1\bigl[b^{(i)}\ge s^{(i+1)}_k\bigr]. \tag{3.4}
--   $$
--   Here $\mathrm{STR}(b,s_k)$ is the ex-post Gains From Trade of Seller Trade Reduction (Definition 2.4).
--
--   This pointwise bound turns the trade-reduction rule into a sum of rank-wise terms, the first step of the decomposition of $\mathrm{STR}(m,n+2)-\mathrm{OPT}(m,n)$.
--
--   Differences from the source: none.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.2, p.12, eq. (3.4); proof p.23

import Mathlib
import Definitions.Def_RecruitSmaller_buyerOrd
import Definitions.Def_RecruitSmaller_sellerOrd
import Definitions.Def_RecruitSmaller_strEx

namespace RecruitSmaller

/-- **Lemma 3.2** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), p.12, eq. (3.4); proof p.23): for any `m ≥ n ≥ 1`, any
`k ≥ n + 1` and any realization `(b, sₖ) ∈ ℝᵐ × ℝᵏ`,
`STR(b, sₖ) ≥ ∑_{i=1}^n (b⁽ⁱ⁾ − s⁽ⁱ⁾ₖ) 𝟙[b⁽ⁱ⁾ ≥ s⁽ⁱ⁺¹⁾ₖ]`.

**Formalization Note** `STR(b, sₖ)` is `strEx`, defined from the trade count `t` of Definition 2.4,
not from the indicator sum. -/
theorem lemma_3_2 (m n k : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hk : n + 1 ≤ k)
    (b : Fin m → ℝ) (s : Fin k → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, (buyerOrd b i - sellerOrd s i) *
        (if sellerOrd s (i + 1) ≤ buyerOrd b i then (1 : ℝ) else 0) ≤ strEx b s := by sorry

end RecruitSmaller
