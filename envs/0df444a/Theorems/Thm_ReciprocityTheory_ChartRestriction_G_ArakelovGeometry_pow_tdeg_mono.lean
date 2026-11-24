-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pow_tdeg_mono
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pow_tdeg_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:17.248352+00:00
-- url     : https://prove2.me/theorems/6a192235-8344-4f9a-9775-e099cc6e19b7
-- title:
--   Arakelov Geometry: pow tdeg mono
-- statement:
--   The Arakelov Geometry construction uses the pow tdeg mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IsMultiHomogX.lean#L28-L31

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pow_tdeg_mono {a b : K → ℕ} (h : tdeg a ≤ tdeg b) (m : ℕ) :
    ((tdeg a : ℝ) + 1) ^ m ≤ ((tdeg b : ℝ) + 1) ^ m := by sorry
