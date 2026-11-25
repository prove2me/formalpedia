-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:35.985196+00:00
-- url     : https://prove2.me/theorems/8b398b15-e4ba-4799-907f-690db46f0be3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  5d0c5493ce4a: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  5d0c5493ce4a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  5d0c5493ce4a construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib cont Diff At eval  5d0c5493ce4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L377-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L377-L389

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ι → ℂ) (e₀ : E) (hg : ∀ i, ContDiffAt ℂ 1 (fun e => g e i) e₀)
    (G : MvPolynomial ι ℤ) : ContDiffAt ℂ 1 (fun e => eval₂ (Int.castRingHom ℂ) (g e) G) e₀ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«contDiffAt_eval₂» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_contDiffAt_eval__5d0c5493ce4a
