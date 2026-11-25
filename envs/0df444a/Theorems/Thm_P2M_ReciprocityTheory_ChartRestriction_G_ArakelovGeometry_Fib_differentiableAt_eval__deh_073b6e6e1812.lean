-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_differentiableAt_eval__deh_073b6e6e1812
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_differentiableAt_eval__deh_073b6e6e1812
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:02.462661+00:00
-- url     : https://prove2.me/theorems/9b0b53f0-0d8e-594e-a942-66e97a7669e1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib differentiable At eval  deh 073b6e6e1812: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib differentiable At eval  de
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib differentiable At eval  deh 073b6e6e1812 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib differentiable At eval  deh 073b6e6e1812 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L407-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L407-L415

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_differentiableAt_eval__deh_073b6e6e1812 {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : DifferentiableAt ℂ t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    DifferentiableAt ℂ (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«differentiableAt_eval₂_deh» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_differentiableAt_eval__deh_073b6e6e1812
