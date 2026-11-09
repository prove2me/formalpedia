-- Prove2me | Theorems.Thm_PhyloCSP_lemma_7_11
-- name    : PhyloCSP.lemma_7_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:53.793607+00:00
-- url     : https://prove2.me/theorems/910fab31-7730-461f-a3b8-6206f9e483f3
-- title:
--   Lemma 7.11 — convexity is the never-between test
-- statement:
--   Let $T$ be a finite rooted binary tree with rooted-triplet relation $C_T$ and $<$ a total order on its leaves. Then $<$ is $C_T$-convex (every internal node's leaf set is an interval) if and only if, for all distinct leaves $a,b,c$,
--   $$
--   a\mid bc\ \Longrightarrow\ a\text{ is not between }b\text{ and }c\text{ with respect to }<.
--   $$
--
--   This test is used throughout Sections 9–10, in particular to recover the output tree from sampled orders (Lemma 10.1).
--
--   Differences from the source:
--   - encoding: a total order < on the leaves; internal nodes of T → a strict total order relation lt; internal nodes as clusters {a, b} ∪ {z : ¬ C(z; a, b)} with a ≠ b; reason: for a binary tree every internal node is the lowest common ancestor of two leaves
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Lemma 7.11, p.23 (PDF p.25); Definition 7.10

import Mathlib
import Definitions.Def_PhyloCSP_Pattern
import Definitions.Def_PhyloCSP_IsConvexOrder

set_option autoImplicit false

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Lemma 7.11, p.23 (PDF p.25): "A total order < is
C_T-convex if and only if, whenever a | bc, the point a is not between b and c w.r.t. the order <."
(Definition 7.10: every internal node's leaf set is an interval.)

**Formalization Note.** `T` is a pattern (finite rooted binary tree) on a finite leaf type; the
total order is a strict total order `lt`; `a | bc` ranges over distinct `a, b, c`. -/
theorem lemma_7_11 {X : Type} [Finite X] (T : Pattern X) (lt : X → X → Prop)
    [IsStrictTotalOrder X lt] :
    IsConvexOrder T.1 lt ↔
      ∀ a b c : X, a ≠ b → a ≠ c → b ≠ c → T.1 a b c = true → ¬ Between lt a b c := by sorry

end PhyloCSP
