-- Prove2me | Theorems.Thm_WeldedPath_Supplement_localized_class_budgets
-- name    : WeldedPath.Supplement.localized_class_budgets
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-22T16:21:43.319301+00:00
-- url     : https://prove2.me/theorems/7d30e19f-f9c4-45f8-9db8-e716d49916a3
-- title:
--   Record cutoff and enlarged boundary for a small permuted edge class
-- statement:
--   Let $G$ be a valid welded-tree instance of even height $n\ge 16$, let $2\le\ell\le n-4$ and $t\le 6q$, and put $N=2^n$. For any permuted edge class with size $s$, enlarge the original boundary by both sets of endpoints of the class, obtaining $B$. Assume
--   $$256(q+1)\le 2^{n-\ell},\qquad 576\left((q+1)2^{-\ell}+(n+1)(q+1)^3/N\right)\le\tfrac12.$$
--   Then $4(t+16)\le s$. If $64(t+6)s\le N$, the enlarged boundary is disjoint from the weld and satisfies
--   $$8(t+6)|B|/N\le\tfrac12.$$
--   These inequalities justify the class cutoffs and boundary conditions used in the localized exact-query comparison.
-- source:
--   Carolan et al., Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, Proposition 4.12, class cutoff and small-class boundary estimate, using Observation 3.3. https://arxiv.org/html/2611.05912v1#S4.SS3

import Mathlib
import Definitions.Def_WeldedPath_Supplement_projGood

namespace WeldedPath.Supplement

theorem localized_class_budgets (n l q t : ℕ) (hn : Even n) (hn16 : 16 ≤ n)
    (hl : 2 ≤ l) (hln : l ≤ n - 4) (ht : t ≤ 6 * q)
    (G : WeldedInstance n) (hG : G.IsValid)
    (hrecords : 256 * ((q : ℝ) + 1) ≤ (2 : ℝ) ^ (n-l))
    (hboundary : 576 * (((q : ℝ) + 1) / (2 : ℝ) ^ l +
      ((n : ℝ) + 1) * ((q : ℝ) + 1) ^ 3 / (2 : ℝ) ^ n) ≤ 1 / 2)
    (b : PClass n l) :
    let s := classSize l G b
    let R := (G.classEdges l b.val).image Edge.tail ∪ (G.classEdges l b.val).image (Edge.head n)
    let B := Vbd n l ∪ R
    4 * (t + 16) ≤ s ∧
      (64 * ((t : ℝ) + 6) * (s : ℝ) ≤ (2 : ℝ)^n →
        Disjoint B (Vweld n) ∧ 8 * ((t : ℝ) + 6) * (B.card : ℝ) / (2 : ℝ)^n ≤ 1 / 2) := by sorry

end WeldedPath.Supplement
