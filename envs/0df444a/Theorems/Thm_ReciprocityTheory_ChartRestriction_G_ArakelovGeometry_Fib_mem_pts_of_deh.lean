-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_mem_pts_of_deh
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.mem_pts_of_deh
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:31.958789+00:00
-- url     : https://prove2.me/theorems/e5bd4eba-5cb4-4cc6-b3fe-90be1cdc5391
-- title:
--   Fib: mem pts of deh
-- statement:
--   The Fib construction uses the mem pts of deh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L94-L108

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.mem_pts_of_deh {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] (x : ι → Ω) (z : ι → ℂ)
    (i₀ : ι) (hx : x i₀ ≠ 0) (hz : z i₀ ≠ 0)
    (h : ∀ G : MvPolynomial ι ℤ, deh x i₀ G = 0 → deh z i₀ G = 0) :
    z ∈ pts (coordIdeal ℤ x) := by sorry
