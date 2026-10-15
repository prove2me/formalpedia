-- Prove2me | Theorems.Thm_SwitchbackExp_CLT_block_variance_bound
-- name    : SwitchbackExp.CLT.block_variance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:08.326797+00:00
-- url     : https://prove2.me/theorems/af344889-ea59-48b2-8cfa-7117fe7696a1
-- title:
--   EC.4.4, proof of Theorem 3, p. ec27 — B²_{n,k,a} = Var(∑_{i=a}^{a+k−1} X_{n,i}) ≤ 16kB²/(n − 1)²
-- statement:
--   Let $m\ge1$, $n\ge4$, $T=nm$, and let the potential outcomes satisfy $|Y_t(w)|\le B$ for all $t\in[T]$ and all paths, with $B>0$ (Assumption 3). Under the optimal design $\mathbb T^*$ with fair coins put $X_{n,i}=\bar{\mathbb 1}_{i-1}/((n-1)m)$ for $i=1,\dots,n-1$. For all integers $a\ge1$ and $k\ge1$ with $a+k-1\le n-1$, the variance
--   $$B^2_{n,k,a}=\mathrm{Var}\Big(\sum_{i=a}^{a+k-1}X_{n,i}\Big)$$
--   satisfies
--   $$B^2_{n,k,a}\le\frac1{(n-1)^2m^2}\Big\{\sum_{i=a}^{a+k-1}\big[3\bar Y_{i-1}(\mathbf 1_{m+1})^2+3\bar Y_{i-1}(\mathbf 0_{m+1})^2+2\bar Y_{i-1}(\mathbf 1_{m+1})\bar Y_{i-1}(\mathbf 0_{m+1})\big]+\sum_{i=a}^{a+k-2}2\big[\bar Y_{i-1}(\mathbf 1_{m+1})+\bar Y_{i-1}(\mathbf 0_{m+1})\big]\big[\bar Y_i(\mathbf 1_{m+1})+\bar Y_i(\mathbf 0_{m+1})\big]\Big\}$$
--   and
--   $$B^2_{n,k,a}\le\frac{16kB^2}{(n-1)^2}.$$
--
--   This is condition 2 of the Romano–Wolf central limit theorem (Lemma EC.1) with $\gamma=0$ and $K_n=16B^2/(n-1)^2$.
--
--   **Formalization Note** The page displays the chain $B^2_{n,k,a}\le\{\cdots\}\le(8km^2B^2+8(k-1)m^2B^2)/((n-1)^2m^2)\le16kB^2/(n-1)^2$; the first and the last bound are stated. For $k=1$ the second inner sum is empty. The variance is Mathlib's `variance` under the uniform measure on the coins.
-- source:
--   arXiv:2009.00148v4, EC.4.4, proof of Theorem 3, p. ec27, display for B²_{n,k,a}

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_CLT_Setting

open SwitchbackExp.Design

namespace SwitchbackExp.CLT

open MeasureTheory ProbabilityTheory

/-- EC.4.4, proof of Theorem 3, p. ec27: with `X_{n,i} = 𝟙̄_{i−1}/((n − 1) m)`, the variance
`B²_{n,k,a}` of `∑_{i=a}^{a+k−1} X_{n,i}` is at most the bracket of the page, and at most
`16 k B² / (n − 1)²` when the potential outcomes are bounded by `B`. -/
theorem block_variance_bound (m n : ℕ) (hm : 1 ≤ m) (hn : 4 ≤ n) (Y : Outcomes) (B : ℝ) (hB : 0 < B)
    (hA3 : Bounded B (n * m) Y)
    (a k : ℕ) (ha : 1 ≤ a) (hk : 1 ≤ k) (hak : a + k ≤ n) :
    variance (fun c : Coins m n => ∑ i ∈ Finset.Icc a (a + k - 1),
        blockErr m (optPoints m n) half Y (i - 1) (pathOf (optPoints m n) c) / (((n : ℝ) - 1) * m))
        (coinMeasure m n)
      ≤ 1 / (((n : ℝ) - 1) ^ 2 * (m : ℝ) ^ 2) *
          (∑ i ∈ Finset.Icc a (a + k - 1),
              (3 * blockSum1 m Y (i - 1) ^ 2 + 3 * blockSum0 m Y (i - 1) ^ 2
                + 2 * blockSum1 m Y (i - 1) * blockSum0 m Y (i - 1))
            + ∑ i ∈ Finset.Icc a (a + k - 2),
              2 * (blockSum1 m Y (i - 1) + blockSum0 m Y (i - 1)) * (blockSum1 m Y i + blockSum0 m Y i)) ∧
    variance (fun c : Coins m n => ∑ i ∈ Finset.Icc a (a + k - 1),
        blockErr m (optPoints m n) half Y (i - 1) (pathOf (optPoints m n) c) / (((n : ℝ) - 1) * m))
        (coinMeasure m n)
      ≤ 16 * k * B ^ 2 / ((n : ℝ) - 1) ^ 2 := by sorry

end SwitchbackExp.CLT
