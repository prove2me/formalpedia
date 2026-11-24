-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:02.061819+00:00
-- url     : https://prove2.me/theorems/45b9c068-174b-4162-839d-0ff2e40c7e7b
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  homog a4d5e8660c60: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  homog a4d5e8660c60
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  homog a4d5e8660c60 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib eval  homog a4d5e8660c60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStA.lean#L27-L44

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60 {ι S : Type*} [Fintype ι] [DecidableEq ι] [Field S] (v : ι → S) (i₀ : ι)
    (hv : v i₀ ≠ 0) {N : ℕ} (G : MvPolynomial ι ℤ) (hN : G.totalDegree ≤ N) :
    eval₂ (Int.castRingHom S) v (homog i₀ N G) = v i₀ ^ N * deh v i₀ G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«eval₂_homog» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_eval__homog_a4d5e8660c60
