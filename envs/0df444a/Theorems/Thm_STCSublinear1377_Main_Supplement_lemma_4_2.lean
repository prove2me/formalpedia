-- Prove2me | Theorems.Thm_STCSublinear1377_Main_Supplement_lemma_4_2
-- name    : STCSublinear1377.Main.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:26:27.972334+00:00
-- url     : https://prove2.me/theorems/883d7e7a-af1b-4822-982d-77bbf329de52
-- title:
--   Lemma 4.2 — Gap of the gadget graph H_A and extraction of a routing
-- statement:
--   Let $Q$ with pairs $(s_1,t_1),\dots,(s_p,t_p)$ be a restricted disjoint-path instance: $Q$ connected and simple, maximum degree at most three, the $2p$ terminals distinct, and exactly the terminals of degree one. Let $A\ge2$ be an integer, $M_Q=|E(Q)|$, $B=\max\{M_Q,2\}$, and let $H_A$ be the weighted graph (4.1). Then:
--
--   1. if the instance is a YES instance, $\mathrm{STC}_w(H_A)\le A+B$;
--   2. there is one polynomial-time algorithm which, given $Q$, the pairs, $A$ and any spanning tree $R$ of $H_A$ with $c_w(H_A,R)<2A$, outputs mutually vertex-disjoint simple paths joining $s_i$ to $t_i$ for all $i$;
--   3. consequently, if the instance is a NO instance, $\mathrm{STC}_w(H_A)\ge 2A$.
--
--   Taking $A$ large relative to $B/\varepsilon$ turns this gap into the hardness of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: the instance, the gadget graph, the tree and the routing → Q as an adjacency table on Fin n, pairs as a list, H_A on Fin (n + pA), binary encodings of instance, tree table and path lists; reason: same instances; the input contains the tree table, whose size is polynomial in |V(H_A)|
--   - generalization: instances with at least one terminal pair (p.16: instances with no terminal pair are decided directly) → every restricted instance, including p = 0; reason: for p = 0 the instance is YES, H_A = Q with unit weights and STC_w(Q) ≤ M_Q ≤ B, the extraction returns the empty routing and the NO clause is vacuous, so every source instance (p ≥ 1) is covered
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Lemma 4.2 and (4.2), PDF/printed p.16; proof pp.16–17

import Definitions.Def_STCSublinear1377_Main_Supplement_Gadget
set_option autoImplicit false

namespace STCSublinear1377.Main.Supplement

/-- Lemma 4.2: the YES bound `A + B` with `B = max{M_Q, 2}`, polynomial-time extraction of a routing
from every spanning tree of congestion below `2A`, and the NO bound `2A`. -/
theorem lemma_4_2 :
    (∀ n : ℕ, ∀ q : Table n, ∀ pairs : List (Fin n × Fin n), ∀ A : ℕ,
      IsRestrictedInstance q pairs → 2 ≤ A → IsYes q pairs →
        stcW (gadget q pairs A) ≤ (A : ℝ) + ((max (edgeCount q) 2 : ℕ) : ℝ)) ∧
    (∃ ext : BinaryEvaluator, ∀ n : ℕ, ∀ q : Table n, ∀ pairs : List (Fin n × Fin n),
      ∀ A : ℕ, IsRestrictedInstance q pairs → 2 ≤ A →
      ∀ R : Table (n + pairs.length * A), (gadget q pairs A).tree R →
        (gadget q pairs A).congestion R < 2 * (A : ℝ) →
        ∃ paths : List (List (Fin n)),
          ext.eval (instanceBits q pairs A ++ tableBits R) = pathsBits paths ∧
          IsRouting q pairs paths) ∧
    (∀ n : ℕ, ∀ q : Table n, ∀ pairs : List (Fin n × Fin n), ∀ A : ℕ,
      IsRestrictedInstance q pairs → 2 ≤ A → ¬ IsYes q pairs →
        2 * (A : ℝ) ≤ stcW (gadget q pairs A)) := by sorry

end STCSublinear1377.Main.Supplement
