-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_homog_isHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.homog_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:47.460545+00:00
-- url     : https://prove2.me/theorems/79e26d07-4689-4536-97df-c49e57bf375e
-- title:
--   Fib: homog is Homogeneous
-- statement:
--   The Fib construction uses the homog is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L17-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.homog_isHomogeneous {ι : Type*} [DecidableEq ι] (i₀ : ι) {N : ℕ} (G : MvPolynomial ι ℤ)
    (hN : G.totalDegree ≤ N) : (homog i₀ N G).IsHomogeneous N := by sorry
