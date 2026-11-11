-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_richness_minor
-- name    : SymmetricDepthHierarchy.ConstantDepth.richness_minor
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:42.435967+00:00
-- url     : https://prove2.me/theorems/882751d4-209a-4c0d-a2fe-871448d2d967
-- title:
--   Lemma B.13: a connected graph with a $(\Delta,k)$-rich minor is $(\Delta,k)$-rich
-- statement:
--   Let $\Delta,k\ge1$. If a connected finite graph $F$ has a $(\Delta,k)$-rich minor $P$, then $F$ is $(\Delta,k)$-rich.
--
--   Together with Theorem B.17 this shows that the non-rich graphs form a minor-closed class.
--
--   Differences from the source:
--   - encoding: P is a minor of F → HadwigerConj.IsMinor P F (disjoint connected branch sets, an edge between the branch sets of adjacent vertices); reason: the standard branch-set definition of a minor, as used in the source's proof
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 34 (PDF p. 37), Lemma B.13

import Mathlib
import Definitions.Def_HadwigerConj_Defs
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma B.13, printed p. 34 (PDF p. 37). Let `Δ, k ≥ 1`. If a connected graph `F` has a
`(Δ, k)`-rich minor, then `F` is `(Δ, k)`-rich. -/
theorem richness_minor (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) {V W : Type} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (hF : F.Connected) (P : SimpleGraph W) (hP : Rich Δ k P)
    (hPF : HadwigerConj.IsMinor P F) : Rich Δ k F := by sorry

end SymmetricDepthHierarchy.ConstantDepth
