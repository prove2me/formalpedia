-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_full_tree_forestwidth
-- name    : SymmetricDepthHierarchy.ConstantDepth.full_tree_forestwidth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:41.272201+00:00
-- url     : https://prove2.me/theorems/b0c4ff2c-784a-499b-bdbb-36c1f6197593
-- title:
--   Example 3.4: $\mathrm{fw}_{\Delta+1}(T_{\Delta,k})=1$ whereas $\mathrm{fw}_\Delta(T_{\Delta,k})\ge k-1$
-- statement:
--   Let $\Delta,k\ge1$ and let $T_{\Delta,k}$ be the full $k$-ary tree of depth $\Delta$. Then
--   $$\mathrm{fw}_{\Delta+1}(T_{\Delta,k})=1\qquad\text{whereas}\qquad \mathrm{fw}_\Delta(T_{\Delta,k})\ge k-1.$$
--
--   One more level of depth collapses the forestwidth of the full tree from about $k$ to $1$; this is the combinatorial gap behind the depth hierarchy.
--
--   Differences from the source:
--   - encoding: T_{Δ,k}: the full k-ary tree of depth Δ → vertices: words of length 0,…,Δ over Fin k (Σ j : Fin (Δ+1), List.Vector (Fin k) j), each word adjacent to its one-letter extensions; reason: the standard model of the full k-ary tree of depth Δ
--   - encoding: fw_Δ(T) ≥ k − 1 → (k : ℕ∞) ≤ forestwidth Δ T + 1; reason: avoids truncated subtraction; identical for k ≥ 1
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 10 (PDF p. 13), Example 3.4 (citing [Bha+25, Theorem 17])

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Example 3.4 ([Bha+25, Theorem 17]), printed p. 10 (PDF p. 13). Let `Δ, k ≥ 1` and let
`T_{Δ,k}` be the full `k`-ary tree of depth `Δ`. Then `fw_{Δ+1}(T_{Δ,k}) = 1` whereas
`fw_Δ(T_{Δ,k}) ≥ k − 1` (stated as `k ≤ fw_Δ(T_{Δ,k}) + 1`). -/
theorem full_tree_forestwidth (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    forestwidth (Δ + 1) (fullTree Δ k) = 1 ∧
      (k : ℕ∞) ≤ forestwidth Δ (fullTree Δ k) + 1 := by sorry

end SymmetricDepthHierarchy.ConstantDepth
