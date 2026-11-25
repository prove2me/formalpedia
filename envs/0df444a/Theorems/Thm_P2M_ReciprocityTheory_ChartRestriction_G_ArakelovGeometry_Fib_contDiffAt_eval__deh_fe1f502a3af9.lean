-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:19.152694+00:00
-- url     : https://prove2.me/theorems/7cf5e70d-41d2-4375-b7a8-60f0095245fd
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  deh fe1f502a3af9: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  deh fe1f502a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  deh fe1f502a3af9 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  deh fe1f502a3af9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L397-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L397-L405

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9 {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (t : E → ℂ) (e₀ : E) (i₀ : ι) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (ht : ContDiffAt ℂ 1 t e₀) (h0 : g e₀ i₀ ≠ 0) (H : Polynomial (MvPolynomial ι ℤ)) :
    ContDiffAt ℂ 1 (fun e => H.eval₂ (deh (g e) i₀) (t e)) e₀ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«contDiffAt_eval₂_deh» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__deh_fe1f502a3af9
