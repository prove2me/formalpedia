-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_walk_bound
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.walk_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:19.395805+00:00
-- url     : https://prove2.me/theorems/f0badeac-aad7-4fae-819e-368cb473dbe9
-- title:
--   Arakelov Geometry: walk bound
-- statement:
--   The Arakelov Geometry construction uses the walk bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L72-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L72-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.walk_bound [DecidableEq K] (Δ : (K → ℕ) → ℝ) (a₁ m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ a : K → ℕ, ∀ b, (∀ k, a₁ ≤ a k) → a₁ < a b →
      |Δ a - Δ (a - Pi.single b 1)| ≤ B * m * ((tdeg a : ℝ) + 1) ^ (m - 1)) :
    ∀ a : K → ℕ, (∀ k, a₁ ≤ a k) →
      |Δ a| ≤ |Δ (fun _ => a₁)| + B * m * tdeg a * ((tdeg a : ℝ) + 1) ^ (m - 1) := by sorry
