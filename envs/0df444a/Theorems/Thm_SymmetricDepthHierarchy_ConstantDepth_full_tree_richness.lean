-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_full_tree_richness
-- name    : SymmetricDepthHierarchy.ConstantDepth.full_tree_richness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:45.340506+00:00
-- url     : https://prove2.me/theorems/9c093769-0f1c-4760-83de-3faaccbb57ac
-- title:
--   Example B.12: the full $(k+1)$-ary tree $T_{\Delta,k+1}$ is $(\Delta,k)$-rich
-- statement:
--   Let $\Delta,k\ge1$. The full $(k+1)$-ary tree $T_{\Delta,k+1}$ of depth $\Delta$ is $(\Delta,k)$-rich.
--
--   It supplies the rich minor of $T_{\Delta,n}$ used in the lower clause of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: T_{Δ,k}: the full k-ary tree of depth Δ → vertices: words of length 0,…,Δ over Fin k (Σ j : Fin (Δ+1), List.Vector (Fin k) j), each word adjacent to its one-letter extensions; reason: the standard model of the full k-ary tree of depth Δ
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 34 (PDF p. 37), Example B.12 (citing [Bha+25])

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Example B.12 ([Bha+25]), printed p. 34 (PDF p. 37). Let `Δ, k ≥ 1`. The full `(k+1)`-ary tree
`T_{Δ,k+1}` of depth `Δ` is `(Δ, k)`-rich. -/
theorem full_tree_richness (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) :
    Rich Δ k (fullTree Δ (k + 1)) := by sorry

end SymmetricDepthHierarchy.ConstantDepth
