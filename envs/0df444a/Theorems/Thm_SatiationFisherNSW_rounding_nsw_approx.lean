-- Prove2me | Theorems.Thm_SatiationFisherNSW_rounding_nsw_approx
-- name    : SatiationFisherNSW.rounding_nsw_approx
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:53.124397+00:00
-- url     : https://prove2.me/theorems/5ed718ae-6fdc-44e6-81ce-135efd345b8b
-- title:
--   Theorem 4.2 — rounding a market equilibrium is a $2e^{1/(2e)}$-approximation for budget-additive Nash social welfare
-- statement:
--   Let $v_{ij}\ge0$, $c_i>0$ be an instance of Nash social welfare with budget-additive valuations on finite sets $B$ of agents and $G$ of items, $n=|B|$. Let $(x,p)$ be any thrifty and modest equilibrium of its Fisher market ($u_{ij}=\min(v_{ij},c_i)$, $m_i=d_j=1$), and let $S$ be the integral allocation produced by any run of the rounding procedure on $(x,p)$. Then for every integral allocation $S^*$,
--   $$
--   \prod_{i\in B}v_i(S^*)\le\bigl(2e^{1/(2e)}\bigr)^{n}\prod_{i\in B}v_i(S),
--   \qquad\text{and}\qquad 2e^{1/(2e)}<2.404 .
--   $$
--   Equivalently, the Nash social welfare of $S$ is at least $1/(2e^{1/(2e)})$ times the optimum.
--
--   Together with an algorithm computing an (approximate) equilibrium, this is the first constant-factor approximation for maximizing Nash social welfare with budget-additive valuations (abstract, p.1; §1.1, p.3).
--
--   **Formalization Note** Every choice of the procedure (roots, largest children, greedy picks) is covered, and a valid run exists only when the allocation graph is a forest. The constant is $2\exp(1/(2e))$.
--
--   Differences from the source:
--   - generalization: §4.1 assumes the market of the instance is money clearing (p.24) and $m\ge n$ (p.7) → neither is a hypothesis; reason: without money clearing every integral allocation has $\prod_iv_i(S^*)=0$ (Lemma 4.2) and the bound holds; $m<n$ violates money clearing since $m_i=d_j=1$; on money-clearing instances with $m\ge n$ the statement is the paper's
--   - encoding: the procedure runs on truncated values $v\le c$ (Lemma 4.1) normalized according to $p$ (p.24), and the guarantee is for the original instance → the market uses $u_{ij}=\min(v_{ij},c_i)$, the procedure reads unnormalized values, and valuations are those of the original $v$; reason: Lemma 4.1 makes integral valuations equal; the thresholds $m^a_i/2<p_j$ and $u_{ij}x_{ij}>c_i/2$ and the greedy pick are unchanged by the rescaling of p.24, which also changes neither the equilibrium nor the optimum
--   - reading: "Without loss of generality, we may assume that the allocation graph … is a forest [45, 23]" (p.26) → the statement covers the equilibria for which the procedure runs, i.e. whose allocation graph is a forest (a valid run exists only then); reason: the procedure and its analysis are defined on forests; the reduction to a forest is cited, not part of the procedure
--   - encoding: "a $2e^{1/2e}$-approximation for the optimal Nash social welfare" (geometric means) → $\prod_iv_i(S^*)\le(2e^{1/(2e)})^{n}\prod_iv_i(S)$ for every integral $S^*$; reason: raising nonnegative geometric means to the power $n$ is monotone, and bounding every allocation is the same as bounding a maximizer; the page prints $2e^{1/2e}$, which is $2e^{1/(2e)}$ (pp.23, 25, and $x=1/(2e)$ on p.29)
--   - reading: a demand bundle maximizes $u_i(\mathbf x_i)$ over bundles with $\sum_j p_jx_{ij}\le m_i$, bundles having $x_{ij}\in[0,1]$ (p.6) → the maximum is taken over all $y\ge 0$ with $\sum_j p_jy_j\le m_i$, without the box $y_j\le 1$; reason: with the box Lemma 4.3(a) fails (one agent, one item, $v=1$, $c=5$, $p=1/2$, $x=1$ would be an equilibrium in which the uncapped agent spends $1/2$); the paper computes the maximal utility as $\min\{c_i,m_i\alpha_i\}$ (proof of Lemma 3.5, p.14), the unboxed maximum; unit supply is enforced by $x_j\le e_j$
--   - reading: an allocation has $\sum_{i}x_{ij}=1$ for every good (p.6) → only $\sum_i x_{ij}\le e_j$ (Definition 2.1 (3)); reason: Definition 2.1 (3) and (5) force $x_j=e_j<1$ when $p_j>d_j$, and Proposition 3.1 (Property 1) has $x_{11}=1/2$
--   - encoding: $j$ is an MBB good of $i$ if $u_{ij}/p_j=\alpha_i$, with $\alpha_i=\infty$ for buyers interested in a zero-price good and $0/0=0$ (p.6) → $u_{ij}>0$ and $u_{ik}p_j\le u_{ij}p_k$ for all $k$; reason: no $\infty$ in $\mathbb R$; the same MBB goods for every buyer with some positive value; it differs only for a buyer whose values are all $0$, who then buys nothing (such a buyer violates money clearing, and in the goal makes every product $0$)
--   - encoding: modest supply $e_j=\min(1,d_j/p_j)$ (p.6) → $e_j=1$ when $p_j=0$, else $\min(1,d_j/p_j)$; reason: at $p_j=0$ the paper's $d_j/p_j$ is $+\infty$, while Lean's $d_j/0$ is $0$
--   - encoding: an integral allocation $S=(S_1,\dots,S_n)$ with characteristic vector $x^S$ (p.7) → a map $S:G\to$ `Option B` giving each item to at most one agent; reason: valuations are monotone, so allowing unassigned items changes no maximum and no bound
--   - encoding: the procedure of §4.1.2 (pp.26–27) and Appendix B (pp.33–34), with arbitrary root choice and tie-breaks, run recursively → a relation `RoundingRun.IsValid` on the choices (an orientation of the allocation forest from root agents, a largest child per good, a greedy pick per agent), the kept child forced by the threshold, and the output defined from the recursion path; reason: the choices are exactly those the paper leaves free, and every valid run is covered; the recursion of Rounding (b) assigns the picked goods along the path to their parents and every other remaining good to its child agent
-- source:
--   Garg, Hoefer, Mehlhorn, Satiation in Fisher markets and approximation of Nash social welfare, arXiv:1707.04428v3 (31 Jul 2019), https://arxiv.org/abs/1707.04428v3, Theorem 4.2, p.28; proof, p.29; procedure, pp.26–27 and 33–34

import Mathlib
import Definitions.Def_SatiationFisherNSW_NSWInstance
import Definitions.Def_SatiationFisherNSW_RoundingRun
open scoped Classical

namespace SatiationFisherNSW

/-- Theorem 4.2 (Garg, Hoefer, Mehlhorn, arXiv:1707.04428v3, p.28): the rounding procedure gives
a `2e^{1/(2e)}`-approximation for the optimal Nash social welfare with budget-additive
valuations, and `2e^{1/(2e)} < 2.404`.

For every instance (`v_{ij} ≥ 0`, `c_i > 0`), every thrifty and modest equilibrium `(x, p)` of
its Fisher market (`u_{ij} = min(v_{ij}, c_i)`, `m_i = d_j = 1`), every run of the rounding
procedure on it, and every integral allocation `S*`:
`∏_i v_i(S*) ≤ (2e^{1/(2e)})^{|B|} · ∏_i v_i(S)`, where `S` is the output of the run.

**Formalization Note** The `n`-th roots of the paper are cleared: `(∏ v_i(S*))^{1/n} ≤ ρ (∏
v_i(S))^{1/n}` is equivalent to the product form for nonnegative products. Comparing with every
integral allocation is the same as comparing with a maximizer. The paper's §4.1 assumes the
market is money clearing and `m ≥ n`; neither is a hypothesis here, because without money
clearing every integral allocation has product `0` (Lemma 4.2), and `m < n` violates money
clearing. Truncation (Lemma 4.1) and normalization (p.24) are built in: the market uses the
truncated values, and the procedure's rules are invariant under the rescaling. A valid run
exists only when the allocation graph is a forest, the paper's "without loss of generality"
(p.26); every choice of roots, largest children and picks is covered. The constant is
`2 · exp(1/(2e))`. -/
theorem rounding_nsw_approx {B G : Type*} [Fintype B] [Fintype G] (I : NSWInstance B G)
    (x : B → G → ℝ) (p : G → ℝ) (hEq : I.market.IsEquilibrium x p)
    (R : RoundingRun B G) (hR : R.IsValid I.market x p) (S : G → Option B) :
    ∏ i, I.val i S ≤
        (2 * Real.exp (1 / (2 * Real.exp 1))) ^ Fintype.card B *
          ∏ i, I.val i (R.output I.market x p) ∧
      2 * Real.exp (1 / (2 * Real.exp 1)) < 2404 / 1000 := by sorry

end SatiationFisherNSW
