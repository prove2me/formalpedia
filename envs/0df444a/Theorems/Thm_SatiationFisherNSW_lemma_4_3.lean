-- Prove2me | Theorems.Thm_SatiationFisherNSW_lemma_4_3
-- name    : SatiationFisherNSW.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:34.190364+00:00
-- url     : https://prove2.me/theorems/bb8bd2b2-90a3-415f-a778-915b4aab72eb
-- title:
--   Lemma 4.3 — structure of normalized equilibria (corrected: (d) needs $0<p_j<1$)
-- statement:
--   Consider a money-clearing Fisher market with $m_i=1$, $d_j=1$ and $v_{ij}\le c_i$ for all $i,j$, and suppose the valuations are normalized according to a thrifty and modest equilibrium $(x,p)$. Then:
--
--   1. (a) a buyer $i\in B\setminus B_0$ spends $m^a_i=\min(1,c_i)$, i.e. $\sum_j p_jx_{ij}=\min(1,c_i)$; its valuation $v_i(x)=\min(c_i,\sum_jv_{ij}x_{ij})$ equals $m^a_i$; and if $i$ is capped then $c_i\le1$;
--   2. (b) a capped buyer $i$ is allocated at least one unit of goods, $\sum_jx_{ij}\ge1$;
--   3. (c) if $i$ is capped and $j$ is an MBB good of $i$, then $p_j\le1$;
--   4. (d) if $0<p_j<1$, then good $j$ is completely sold, $\sum_ix_{ij}=1$;
--   5. (e) the money spent on good $j$ is $p^a_j=\min(p_j,1)$:
--   $$
--   p_j\sum_{i\in B}x_{ij}=\min(p_j,1).
--   $$
--
--   These facts drive the upper bound of Theorem 4.1 and the analysis of the rounding procedure.
--
--   Differences from the source:
--   - reading: a demand bundle maximizes $u_i(\mathbf x_i)$ over bundles with $\sum_j p_jx_{ij}\le m_i$, bundles having $x_{ij}\in[0,1]$ (p.6) → the maximum is taken over all $y\ge 0$ with $\sum_j p_jy_j\le m_i$, without the box $y_j\le 1$; reason: with the box Lemma 4.3(a) fails (one agent, one item, $v=1$, $c=5$, $p=1/2$, $x=1$ would be an equilibrium in which the uncapped agent spends $1/2$); the paper computes the maximal utility as $\min\{c_i,m_i\alpha_i\}$ (proof of Lemma 3.5, p.14), the unboxed maximum; unit supply is enforced by $x_j\le e_j$
--   - reading: an allocation has $\sum_{i}x_{ij}=1$ for every good (p.6) → only $\sum_i x_{ij}\le e_j$ (Definition 2.1 (3)); reason: Definition 2.1 (3) and (5) force $x_j=e_j<1$ when $p_j>d_j$, and Proposition 3.1 (Property 1) has $x_{11}=1/2$
--   - encoding: $j$ is an MBB good of $i$ if $u_{ij}/p_j=\alpha_i$, with $\alpha_i=\infty$ for buyers interested in a zero-price good and $0/0=0$ (p.6) → $u_{ij}>0$ and $u_{ik}p_j\le u_{ij}p_k$ for all $k$; reason: no $\infty$ in $\mathbb R$; the same MBB goods for every buyer with some positive value; it differs only for a buyer whose values are all $0$, who then buys nothing (such a buyer violates money clearing, and in the goal makes every product $0$)
--   - encoding: modest supply $e_j=\min(1,d_j/p_j)$ (p.6) → $e_j=1$ when $p_j=0$, else $\min(1,d_j/p_j)$; reason: at $p_j=0$ the paper's $d_j/p_j$ is $+\infty$, while Lean's $d_j/0$ is $0$
--   - encoding: "we normalize $v'_{ij}=v_{ij}/\alpha_i$ and $c'_i=c_i/\alpha_i$" for $i\in B\setminus B_0$ and "assume that $v$ and $c$ fulfill these conditions directly" (p.24) → hypothesis `IsNormalized`: every buyer outside $B_0$ has MBB ratio $\alpha_i=\max_k u_{ik}/p_k=1$; reason: the paper's own convention; every normalized instance arises this way and the rescaling preserves money clearing, $v\le c$ and the equilibrium
--   - correction: (d) "If $p_j<1$, $j$ is completely sold" → (d) for $0<p_j<1$; reason: false at $p_j=0$: one agent, two items, $v=(1,1)$, $c=1$, $p=(0,0)$, $x=(1,0)$ is a thrifty and modest equilibrium of a money-clearing market with $v\le c$ (normalization is vacuous since the agent is in $B_0$), and item 2 is unsold; the proof treats "$0<p_j<1$" (p.24)
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Lemma 4.3, p.24 (standing assumptions: $v_{ij}\le c_i$, p.23; money clearing and normalization, p.24)

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

namespace SatiationFisherNSW

/-- Lemma 4.3 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.24), with item (d) corrected to
`0 < p_j < 1`. For a money-clearing Fisher market with `m_i = 1`, `d_j = 1`, `v_{ij} ≤ c_i`, and
valuations normalized according to a thrifty and modest equilibrium `(x, p)`:

* (a) a buyer `i ∈ B \ B₀` spends `m^a_i = min(1, c_i)`, its valuation `v_i(x)` equals
  `m^a_i`, and if `i` is capped then `c_i ≤ 1`;
* (b) a capped buyer is allocated at least one unit of goods;
* (c) if `i` is capped and `j` is an MBB good of `i`, then `p_j ≤ 1`;
* (d) if `0 < p_j < 1`, then `j` is completely sold;
* (e) the money spent on good `j` is `p^a_j = min(p_j, 1)`.

**Formalization Note** The printed (d) reads "If `p_j < 1`"; it fails at `p_j = 0` (one agent,
two items, `v = (1, 1)`, `c = 1`, `p = (0, 0)`, `x = (1, 0)`), and the proof treats
`0 < p_j < 1`. "Spends" is `Σ_j p_j x_{ij}`, "completely sold" is `Σ_i x_{ij} = 1`, and the money
spent on good `j` is `p_j Σ_i x_{ij}`. The fractional valuation `v_i(x)` is the utility
`min(c_i, Σ_j u_{ij} x_{ij})` in the market of the instance, whose values are `v` when `v ≤ c`.
The standing assumptions of §4.1 are hypotheses: `v_{ij} ≤ c_i`
(p.23, "Henceforth"), the market of the instance (`u = v`, `m_i = d_j = 1`) is money clearing
(p.24, "for the remainder of this section"), `(x, p)` is a thrifty and modest equilibrium of it,
and the valuations are normalized according to `p` (MBB ratio `1` for every buyer outside `B₀`,
p.24). -/
theorem lemma_4_3
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p) :
    (∀ i, ¬ I.market.InB0 p i →
      ∑ j, p j * x i j = min 1 (I.c i) ∧ I.market.utility i (x i) = min 1 (I.c i) ∧
        (I.market.IsCapped x i → I.c i ≤ 1)) ∧
    (∀ i, I.market.IsCapped x i → 1 ≤ ∑ j, x i j) ∧
    (∀ i j, I.market.IsCapped x i → I.market.IsMBB p i j → p j ≤ 1) ∧
    (∀ j, 0 < p j → p j < 1 → ∑ i, x i j = 1) ∧
    (∀ j, p j * ∑ i, x i j = min (p j) 1) := by sorry

end SatiationFisherNSW
