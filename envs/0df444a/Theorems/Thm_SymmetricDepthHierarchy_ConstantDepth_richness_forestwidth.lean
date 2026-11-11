-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_richness_forestwidth
-- name    : SymmetricDepthHierarchy.ConstantDepth.richness_forestwidth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:38.477184+00:00
-- url     : https://prove2.me/theorems/84fa87dc-047d-44b1-bdc8-214e4cd37164
-- title:
--   Lemma B.10: a $(\Delta,k)$-rich graph has $\mathrm{fw}_\Delta\ge k$
-- statement:
--   Let $\Delta,k\ge1$. If a finite graph $F$ is $(\Delta,k)$-rich, then
--   $$\mathrm{fw}_\Delta(F)\ge k.$$
--
--   Richness is thus a certificate of large $\Delta$-forestwidth.
--
--   Differences from the source:
--   - encoding: fw_Δ(F) ∈ ℕ → forestwidth Δ F ∈ ℕ∞; reason: for Δ ≥ 1 every finite graph has a decomposition, so the value is finite and equal to the source's
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 34 (PDF p. 37), Lemma B.10

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Richness

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Lemma B.10, printed p. 34 (PDF p. 37). Let `Δ, k ≥ 1`. If a graph `F` is `(Δ, k)`-rich, then
`fw_Δ(F) ≥ k`. -/
theorem richness_forestwidth (Δ k : ℕ) (hΔ : 1 ≤ Δ) (hk : 1 ≤ k) {V : Type} [Fintype V]
    (F : SimpleGraph V) (hF : Rich Δ k F) : (k : ℕ∞) ≤ forestwidth Δ F := by sorry

end SymmetricDepthHierarchy.ConstantDepth
