-- Prove2me | Theorems.Thm_ReLUSynth_Boolean_prop_2_2
-- name    : ReLUSynth.Boolean.prop_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:09:23.96533+00:00
-- url     : https://prove2.me/theorems/cd4c07fe-77e3-497c-ace6-6ac1cf670aed
-- title:
--   Proposition 2.2 — a permitted network has at most m computational vertices, and at most N_H functions are computed by permitted networks
-- statement:
--   Let $W$ be an inventory of $m\ge1$ rational occurrences, $d\ge1$ the input dimension and $n_{\max}\ge1$ the cap. Put $n=\min\{m,n_{\max}\}$, $K=n(d+n+1)$ and
--   $$N_H=(n+1)^2\min\{(K+1)^m,(m+1)^K\}.$$
--   Under either inventory rule, every permitted network has at most $m$ computational vertices, and the class $\mathcal H_{W,n_{\max}}$ of functions $\mathbb R^d\to\mathbb R$ computed by permitted networks is finite with $|\mathcal H_{W,n_{\max}}|\le N_H$.
--
--   The bound gives polynomial-length descriptions of candidate networks, which is what puts the synthesis problems in $\Sigma_2^P$.
--
--   Differences from the source:
--   - encoding: a permitted network is an arbitrary finite DAG with one output vertex → the computational vertices are numbered 0,…,h in a topological order, the output is vertex h, and an edge between computational vertices goes from a lower to a higher number (Pos.hidEdge); reason: every finite DAG has a topological order (p. 9), and the output, which every computational vertex reaches, is last in it; the same networks up to relabeling
--   - encoding: |H_{W,n_max}| ≤ N_H for the class of computed functions → Set.Finite of the set of functions (ι → ℝ) → ℝ computed by permitted networks, and its Set.ncard ≤ N_H; reason: Set.ncard is 0 on an infinite set, so finiteness is stated explicitly
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 11, Proposition 2.2

import Mathlib
import Definitions.Def_ReLUSynth_Boolean_Network

namespace ReLUSynth.Boolean

/-- Proposition 2.2 (p. 11): for an inventory of `m ≥ 1` rational occurrences, `d ≥ 1` inputs and a
cap `n_max ≥ 1`, every permitted network (under either rule) has at most `m` computational
vertices, and the class `H_{W,n_max}` of functions `ℝ^d → ℝ` computed by permitted networks is
finite with at most `N_H = (n+1)^2 min{(K+1)^m, (m+1)^K}` members, where `n = min{m, n_max}` and
`K = n(d + n + 1)`. -/
theorem prop_2_2 {ι α : Type} [Fintype ι] [Fintype α] (W : α → ℚ) (nmax : ℕ)
    (rule : InventoryRule) (hd : 1 ≤ Fintype.card ι) (hm : 1 ≤ Fintype.card α)
    (hnmax : 1 ≤ nmax) :
    (∀ N : Net ι α, N.Permitted rule nmax → N.h + 1 ≤ Fintype.card α) ∧
    ({g : (ι → ℝ) → ℝ | ∃ N : Net ι α, N.Permitted rule nmax ∧
          g = N.eval (fun o => (W o : ℝ))}.Finite ∧
      {g : (ι → ℝ) → ℝ | ∃ N : Net ι α, N.Permitted rule nmax ∧
          g = N.eval (fun o => (W o : ℝ))}.ncard ≤
        (min (Fintype.card α) nmax + 1) ^ 2 *
          min ((min (Fintype.card α) nmax * (Fintype.card ι + min (Fintype.card α) nmax + 1)
                + 1) ^ Fintype.card α)
              ((Fintype.card α + 1) ^ (min (Fintype.card α) nmax *
                (Fintype.card ι + min (Fintype.card α) nmax + 1)))) := by sorry

end ReLUSynth.Boolean
