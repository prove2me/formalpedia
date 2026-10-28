-- Prove2me | Theorems.Thm_SyncPrefix_Huffman_theorem_2_reduction
-- name    : SyncPrefix.Huffman.theorem_2_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:36:48.230571+00:00
-- url     : https://prove2.me/theorems/952dfcc1-7064-43f6-8179-0a279b76993e
-- title:
--   Theorem 2 (proof), p. 5 — the pipe automaton of a Set Cover instance is strongly acyclic with p² + 1 states, and its shortest synchronizing word has the minimum cover size as length
-- statement:
--   Let $X = \{x_1, \dots, x_p\}$ and let $C = (c_1, \dots, c_m)$ be a family of subsets of $X$ that covers $X$. Let $A$ be the pipe automaton of the instance: one letter per set, the states $q^{(j)}_1, \dots, q^{(j)}_p$ for every point $x_j$ and a state $f$, where for $1 \le i \le p-1$ the letter $k$ maps $q^{(j)}_i$ to $f$ if $x_j \in c_k$ and to $q^{(j)}_{i+1}$ otherwise, and every letter maps $q^{(j)}_p$ and $f$ to $f$.
--
--   Then $A$ has $p^2 + 1$ states and $m$ letters, $A$ is strongly acyclic and synchronizing, and
--   $$\ell(A) = \mathrm{OPT}(X, C),$$
--   the length of a shortest synchronizing word of $A$ equals the minimum size of a subfamily of $C$ covering $X$.
--
--   This is the gap-preserving reduction from Set Cover behind Theorem 2 and, through Lemma 5, behind Corollary 8.
--
--   Differences from the source:
--   - reading: the Set Cover input is a family covering X (the proof: "such subfamily trivially exists if C covers X") → hypothesis `I.Coverable`; reason: without a cover the minimum is undefined.
--   - encoding: states q^{(j)}_i and f → `Fin (p·p + 1)`, with q^{(j+1)}_{i+1} ↦ j·p + i and f ↦ p²; reason: Lean convention, the same automaton.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 5, proof of Theorem 2

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover

/-- Theorem 2's reduction (p. 5): for a Set Cover instance in which every point lies in some set,
the pipe automaton has `p² + 1` states and one letter per set, is strongly acyclic and
synchronizing, and the length of its shortest synchronizing word is the minimum size of a set
cover. -/
theorem theorem_2_reduction (I : SCInstance) (hI : I.Coverable) :
    (scAutomaton I).n = I.n ^ 2 + 1 ∧ (scAutomaton I).k = I.sets.length ∧
      StronglyAcyclic (scAutomaton I).δ ∧ IsSynchronizing (scAutomaton I).δ ∧
        syncLength (scAutomaton I).δ = minCover I := by sorry

end SyncPrefix.Huffman
