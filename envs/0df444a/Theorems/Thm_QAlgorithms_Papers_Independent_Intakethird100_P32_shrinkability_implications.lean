-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P32_shrinkability_implications
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P32.shrinkability_implications
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:46:42.616035+00:00
-- url     : https://prove2.me/theorems/37957a90-d463-4cc2-b929-d13638112b93
-- title:
--   Implications among shrinkability notions
-- statement:
--   Let $f:X\to B$ be a continuous map between compactly generated Hausdorff spaces. A shrinkable map has a continuous section $s:B\to X$ and a homotopy from $s\circ f$ to $\mathrm{id}_X$ that stays over $B$. Then
--
--   $$\begin{gathered}
--   f\text{ shrinkable}\ \Longrightarrow\ f\text{ is a homotopy equivalence},\\
--   f\text{ shrinkable}\ \Longrightarrow\ f\text{ locally shrinkable}\ \Longrightarrow\ f\text{ $\mathcal{CG}$-locally shrinkable}.
--   \end{gathered}$$
--
--   Local shrinkability uses an open cover of $B$; $\mathcal{CG}$-local shrinkability uses a $\mathcal{CG}$-cover. All restrictions are formed in $\mathrm{CGH}$. The homotopy equivalence in the first assertion has $f$ itself as its forward map.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, PDF p. 28, Remark §4.3: implications between shrinkability notions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- Remark and Definition 4.3, PDF p.28: shrinkable maps are homotopy equivalences,
and shrinkable implies locally shrinkable implies CG-locally shrinkable.
The homotopy equivalence has f itself as its forward map. -/
theorem shrinkability_implications (X B : Type u) [TopologicalSpace X]
    [TopologicalSpace B] [T2Space X] [T2Space B]
    [CompactlyGeneratedSpace X] [CompactlyGeneratedSpace B] (f : C(X, B)) :
    (ShrinkableMap f → ∃ e : ContinuousMap.HomotopyEquiv X B, ∀ x, e x = f x) ∧
    (ShrinkableMap f → LocallyShrinkableMap f) ∧
    (LocallyShrinkableMap f → CGLocallyShrinkableMap f) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P32
