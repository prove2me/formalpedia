-- Prove2me | Theorems.Thm_RemovingTrees_Main_tree_removal_polytime
-- name    : RemovingTrees.Main.tree_removal_polytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:21.729882+00:00
-- url     : https://prove2.me/theorems/1ff1a19c-733f-40b7-9a18-a7acc3c62549
-- title:
--   Theorem 3.1 — Polynomial-time removal with sublinear connectivity loss
-- statement:
--   There is one deterministic finite bit machine and fixed integers $a>0$ and $d\ge0$ that work for every positive integer $k$ and every finite undirected multigraph $G$ on at least two vertices with $\lambda(G)\ge k$. Writing
--   $$
--   h(k)=\sqrt{\max(1,\ln k)},\qquad A=2\sqrt{20\ln44}+89,
--   $$
--   the machine returns a spanning tree $T\subseteq G$ with
--   $$
--   \lambda(G-T)\ge k-\frac{Ak}{h(k)}.
--   $$
--   On the explicit framed binary edge-list input of actual length $L$, it has halted by $a(L+1)^d$ transitions. Its decoded output is a duplicate-free list of original edge identifiers; correctness is about this output, not an uncosted mathematical choice. The same $A$, program, and polynomial precede all graph and parameter quantifiers.
--
--   This is the complete constructive headline theorem, including odd $k$, loops, parallel edges, and polynomial bit complexity. It establishes the stated $O(k/\sqrt{\log k})$ connectivity loss uniformly in graph size.
--
--   **Formalization Note** The numerical envelope is derived from pp.6–7, not printed as a constant in Theorem 3.1. For sufficiently large even $k$ the finer bound is $k-2\sqrt{20\ln44}\,k/\sqrt{\ln k}-88\sqrt{k}$. The fixed threshold $44^{320}$ and the preceding even integer handle the large and odd regimes; below this range the displayed lower bound is nonpositive and an arbitrary polynomial-time spanning tree suffices.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: polynomial-time construction → one finite machine and one polynomial before all inputs, with halting and actual encoded output correctness; reason: makes the computational clause explicit in the framed binary input model
--   - encoding: k − O(k/√log k) → k − A k/√max(1,ln k) for every positive k, with fixed A = 2√(20 ln 44) + 89; reason: the proof gives this uniform envelope; natural logarithm fixes normalization and the bounded initial range avoids division by zero without losing any asymptotic instance
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Theorem 3.1, p.4; quantitative iteration, pp.6–7

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Theorem 3.1, p.4. Uniform bit complexity, all positive k, loops and parallel
edges. The fixed loss constant is the envelope derived from pp.6–7. -/
theorem tree_removal_polytime :
    ∃ A : ℝ, 0 < A ∧ A = lossConstant ∧
    ∃ M : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    ∀ (n m k : ℕ) (G : MultiGraph n m),
      2 ≤ n → 0 < k → CutLower G Finset.univ k →
      BitResult M a d (encNat k ++ encGraph G)
        (TreeOutput G (fun T => CutLower G (Finset.univ \ T)
          ((k:ℝ) - A*k/lossScale k))) := by sorry
end RemovingTrees.Main
