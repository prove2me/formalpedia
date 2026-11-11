-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_weak_oddomorphism_richness
-- name    : SymmetricDepthHierarchy.ConstantDepth.weak_oddomorphism_richness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:33.108471+00:00
-- url     : https://prove2.me/theorems/93b08c4c-0afe-441d-a0b4-51de2f98317c
-- title:
--   Theorem B.17: weak oddomorphisms reflect $(\Delta,k)$-richness
-- statement:
--   Let $\Delta,k\ge1$ and let $\varphi:F\to G$ be a weak oddomorphism between finite graphs. If $G$ is $(\Delta,k)$-rich, then $F$ is $(\Delta,k)$-rich.
--
--   This is the closure property needed to apply the monotonicity theorem to the class of non-rich graphs.
--
--   Differences from the source: none.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 35 (PDF p. 38), Theorem B.17

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Oddomorphism

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem B.17, printed p. 35 (PDF p. 38). Let `Δ, k ≥ 1` and let `φ : F → G` be a weak
oddomorphism. If `G` is `(Δ, k)`-rich, then `F` is `(Δ, k)`-rich. -/
theorem weak_oddomorphism_richness (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) {V W : Type} [Fintype V]
    [Fintype W] (F : SimpleGraph V) (G : SimpleGraph W) (φ : F →g G)
    (hφ : IsWeakOddomorphism φ) (hG : Rich Δ k G) : Rich Δ k F := by sorry

end SymmetricDepthHierarchy.ConstantDepth
