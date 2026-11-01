-- Prove2me | Theorems.Thm_SatiationFisherNSW_theorem_4_1
-- name    : SatiationFisherNSW.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:25.81722+00:00
-- url     : https://prove2.me/theorems/7a8760cb-0740-43a6-b4cf-876c008af650
-- title:
--   Theorem 4.1 — upper bound on the optimal Nash social welfare from equilibrium prices
-- statement:
--   Let the valuations $v\le c$ of a money-clearing instance be normalized according to a thrifty and modest equilibrium $(x,p)$ of its Fisher market, let $B_c$ be the set of capped buyers in $(x,p)$ and $n=|B|$. Then every integral allocation $S$, in particular one $x^*$ maximizing the Nash social welfare, satisfies
--   $$
--   \Bigl(\prod_{i\in B}v_i(S)\Bigr)^{1/n}\le\Bigl(\prod_{i\in B_c}c_i\prod_{j:\,p_j>1}p_j\Bigr)^{1/n}.
--   $$
--
--   This is the benchmark against which the rounded allocation is compared in Theorem 4.2.
--
--   **Formalization Note** The $n$-th roots are real powers with exponent $1/n$; for $n=0$ both sides are $1$.
--
--   Differences from the source:
--   - reading: a demand bundle maximizes $u_i(\mathbf x_i)$ over bundles with $\sum_j p_jx_{ij}\le m_i$, bundles having $x_{ij}\in[0,1]$ (p.6) → the maximum is taken over all $y\ge 0$ with $\sum_j p_jy_j\le m_i$, without the box $y_j\le 1$; reason: with the box Lemma 4.3(a) fails (one agent, one item, $v=1$, $c=5$, $p=1/2$, $x=1$ would be an equilibrium in which the uncapped agent spends $1/2$); the paper computes the maximal utility as $\min\{c_i,m_i\alpha_i\}$ (proof of Lemma 3.5, p.14), the unboxed maximum; unit supply is enforced by $x_j\le e_j$
--   - reading: an allocation has $\sum_{i}x_{ij}=1$ for every good (p.6) → only $\sum_i x_{ij}\le e_j$ (Definition 2.1 (3)); reason: Definition 2.1 (3) and (5) force $x_j=e_j<1$ when $p_j>d_j$, and Proposition 3.1 (Property 1) has $x_{11}=1/2$
--   - encoding: $j$ is an MBB good of $i$ if $u_{ij}/p_j=\alpha_i$, with $\alpha_i=\infty$ for buyers interested in a zero-price good and $0/0=0$ (p.6) → $u_{ij}>0$ and $u_{ik}p_j\le u_{ij}p_k$ for all $k$; reason: no $\infty$ in $\mathbb R$; the same MBB goods for every buyer with some positive value; it differs only for a buyer whose values are all $0$, who then buys nothing (such a buyer violates money clearing, and in the goal makes every product $0$)
--   - encoding: modest supply $e_j=\min(1,d_j/p_j)$ (p.6) → $e_j=1$ when $p_j=0$, else $\min(1,d_j/p_j)$; reason: at $p_j=0$ the paper's $d_j/p_j$ is $+\infty$, while Lean's $d_j/0$ is $0$
--   - encoding: "we normalize $v'_{ij}=v_{ij}/\alpha_i$ and $c'_i=c_i/\alpha_i$" for $i\in B\setminus B_0$ and "assume that $v$ and $c$ fulfill these conditions directly" (p.24) → hypothesis `IsNormalized`: every buyer outside $B_0$ has MBB ratio $\alpha_i=\max_k u_{ik}/p_k=1$; reason: the paper's own convention; every normalized instance arises this way and the rescaling preserves money clearing, $v\le c$ and the equilibrium
--   - encoding: "where $x^*$ is an integral allocation that maximizes the Nash social welfare" → the bound for every integral allocation $S$; reason: a bound for a maximizer bounds every allocation, and conversely
--   - encoding: an integral allocation $S=(S_1,\dots,S_n)$ with characteristic vector $x^S$ (p.7) → a map $S:G\to$ `Option B` giving each item to at most one agent; reason: valuations are monotone, so allowing unassigned items changes no maximum and no bound
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Theorem 4.1, p.25 (standing assumptions: $v_{ij}\le c_i$, p.23; money clearing and normalization, p.24)

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
open scoped Classical

namespace SatiationFisherNSW

/-- Theorem 4.1 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.25): for valuations `v` and caps
`c` normalized according to equilibrium prices `p`,
`(∏_{i∈B} v_i(x*))^{1/n} ≤ (∏_{i∈B_c} c_i ∏_{j : p_j > 1} p_j)^{1/n}`, where `x*` is an integral
allocation that maximizes the Nash social welfare and `B_c` is the set of capped buyers in
`(x, p)`.

**Formalization Note** The bound is stated for every integral allocation `S : G → Option B`,
which is equivalent to stating it for a maximizer `x*`. `n = |B|`, and `(·)^{1/n}` is the real
power `rpow`. The caps of agents in `B₀` are not rescaled by the normalization.
The standing assumptions of §4.1 are hypotheses: `v_{ij} ≤ c_i`
(p.23, "Henceforth"), the market of the instance (`u = v`, `m_i = d_j = 1`) is money clearing
(p.24, "for the remainder of this section"), `(x, p)` is a thrifty and modest equilibrium of it,
and the valuations are normalized according to `p` (MBB ratio `1` for every buyer outside `B₀`,
p.24). -/
theorem theorem_4_1
    {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (hvc : ∀ i j, I.v i j ≤ I.c i) (hMC : I.market.IsMoneyClearing)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p) (hN : I.IsNormalized p)
    (S : G → Option B) :
    (∏ i, I.val i S) ^ (1 / (Fintype.card B : ℝ)) ≤
      ((∏ i ∈ Finset.univ.filter (fun i => I.market.IsCapped x i), I.c i) *
        ∏ j ∈ Finset.univ.filter (fun j => 1 < p j), p j) ^ (1 / (Fintype.card B : ℝ)) := by sorry

end SatiationFisherNSW
