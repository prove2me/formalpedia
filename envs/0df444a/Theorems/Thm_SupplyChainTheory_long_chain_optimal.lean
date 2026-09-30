-- Prove2me | Theorems.Thm_SupplyChainTheory_long_chain_optimal
-- name    : SupplyChainTheory.long_chain_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:13:10.832048+00:00
-- url     : https://prove2.me/theorems/910ad999-fea7-466b-9705-971d0db0d907
-- title:
--   Theorem 7.9: the long chain $C_n$ maximizes expected sales among all 2-flexibility designs
-- statement:
--   **Theorem 7.9.** Consider a balanced system of size $n \ge 2$ with exchangeable demand: $n$
--   products, $n$ plants of equal capacity, and a random demand vector whose joint law is
--   invariant under permutations of the products. A 2-flexibility design is a set of
--   plant-product capabilities in which every plant can produce exactly two products and every
--   product can be produced by exactly two plants; the long chain $C_n$, in which plant $j$ makes
--   products $j$ and $j + 1$ (and plant $n$ makes $n$ and $1$), is one of them. Let $\mathcal{F}_2$
--   be the set of all 2-flexibility designs. Then
--
--   $$ C_n \in \arg\max_{A \in \mathcal{F}_2} [A], $$
--
--   that is, $C_n$ is a 2-flexibility design and $[A] \le [C_n]$ for every 2-flexibility design
--   $A$, where $[A] = \mathbb{E}[P(D, A)]$ is the expected maximum sales under $A$.
--
--   The book's proof: a 2-flexibility design is a disjoint union of closed chains of lengths
--   $n_1, \dots, n_m$ summing to $n$, so $[A] = \sum_j [C_{n_j}] = \sum_j n_j([L_{n_j}] - [L_{n_j - 1}])$
--   by Lemma 7.8; each increment $[L_{n_j}] - [L_{n_j-1}]$ is at most $[L_n] - [L_{n-1}]$ by Lemma
--   7.7 through the identity (7.31), and $\sum_j n_j = n$ gives $[A] \le n([L_n] - [L_{n-1}]) = [C_n]$.
--   This is the analytical explanation of Jordan and Graves's observation that one long chain
--   outperforms several short ones.
--
--   **Formalization Note** Edges are (product, plant) pairs and product indices wrap modulo $n$.
--   The decomposition of a 2-regular bipartite graph into cycles is part of the proof, not of the
--   statement.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 252, Sect. 7.5.3, Theorem 7.9 and its proof, Eq. (7.31); after Simchi-Levi and Wei (2012)

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem long_chain_optimal {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) (hn : 2 ≤ n) :
    TwoFlex (longChain n) ∧ ∀ A : Finset (Fin n × Fin n), TwoFlex A →
      S.expPerf A ≤ S.expPerf (longChain n) := by sorry

end SupplyChainTheory
