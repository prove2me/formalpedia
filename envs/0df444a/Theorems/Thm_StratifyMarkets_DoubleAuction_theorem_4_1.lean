-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_1
-- name    : StratifyMarkets.DoubleAuction.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:47.869377+00:00
-- url     : https://prove2.me/theorems/bfe80118-c231-46d8-9383-9ca47dbc31b2
-- title:
--   Theorem 4.1 — every double auction with independent values and costs admits a worst-rationed stratification with Strat ≥ FB/27843
-- statement:
--   Consider any double auction instance: $n$ buyers and $m$ sellers ($n,m\ge0$), buyer $i$'s value $v_i\sim F_i$ and seller $j$'s cost $c_j\sim G_j$, all $n+m$ values and costs mutually independent, and every $F_i$, $G_j$ a continuous distribution supported on $[0,1]$ (not necessarily identical). Then there is a market stratification $0\le m_0<m_1<\dots<m_N\le1$, $m_{k-1}\le p_k\le m_k$ ($N\ge1$), that applies the worst-rationed rule within each submarket $[m_{k-1},m_k]$ at price $p_k$ and satisfies
--   $$\mathrm{Strat}=\sum_{k=1}^N\mathrm{WorstRationed}(m_{k-1},p_k,m_k)\ge\frac1{27843}\,\mathrm{FB},$$
--   where $\mathrm{FB}=\mathbb E_{\mathbf v,\mathbf c}\big[\sum_{i=1}^{\tau}(v_{(i)}-c_{(i)})\big]$ is the first-best gains from trade. This is the paper's main result; the constant comes from $7+10240e<27843$.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: indices k = 1, …, N → 0-based `k : Fin N`, submarket k is [m k.castSucc, m k.succ] with price p k; reason: relabelling only
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 25, Theorem 4.1 (proof p. 49)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Theorem 4.1 (p. 25): for every double auction instance (any `n` buyers and `m` sellers with
independent continuous values and costs on `[0, 1]`), some stratification that applies the
worst-rationed rule within each submarket satisfies `Strat ≥ FB / 27843`. -/
theorem theorem_4_1 {n m : ℕ} (I : DAInstance n m) :
    ∃ σ : Stratification, 1 / 27843 * I.FB ≤ I.strat σ := by sorry

end StratifyMarkets.DoubleAuction
