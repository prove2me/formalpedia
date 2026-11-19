-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_uniform_block_matching_contains
-- name    : QuantumBipartiteTesting.Bipartiteness.uniform_block_matching_contains
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:14.154029+00:00
-- url     : https://prove2.me/theorems/f56fa7e2-cba8-4bfd-9730-1a1d1334cae5
-- title:
--   Exact prescribed-pair probability for block-preserving perfect matchings
-- statement:
--   Let $l\ge1$ and let $s$ be even. Partition $ls$ labeled vertices into $l$ canonical blocks of size $s$. For each block $j$, prescribe a partial matching $E_j$ of disjoint, nonloop pairs in that block. If $h$ is uniform among fixed-point-free involutions preserving every block, then
--
--   $$
--   \Pr[\text{every }E_j\text{ occurs in }h]
--   =\prod_{j=1}^{l}\prod_{a=0}^{|E_j|-1}(s-2a-1)^{-1}.
--   $$
--
--   This supplies the exact independent-block matching probability used in the hidden-block graph sampling law. Empty blocks and empty partial matchings follow the stated finite-sum conventions.
-- source:
--   Kayal–Sen–Szabó, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, §2.5.1 hidden-block matching distribution and Appendix A.2, printed p.30, probability R_d and product (A.2).

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
open QuantumBipartiteTesting.Bipartiteness Finset
open scoped BigOperators Classical

theorem QuantumBipartiteTesting.Bipartiteness.uniform_block_matching_contains (l s : ℕ) (hl : 0 < l) (hs : Even s)
    (E : Fin l → Finset (Sym2 (Fin s)))
    (hloop : ∀ j, ∀ p ∈ E j, ¬ p.IsDiag)
    (hdisj : ∀ j, ∀ p ∈ E j, ∀ q ∈ E j, (∃ x, x ∈ p ∧ x ∈ q) → p = q) :
    Average (Matchings (l*s) l) (fun h =>
      if ∀ j a b, s(a,b) ∈ E j → h (finProdFinEquiv (j,a)) = finProdFinEquiv (j,b) then (1:ℝ) else 0) =
      ∏ j, ∏ a ∈ range (E j).card, ((s:ℝ)-2*a-1)⁻¹ := by sorry
