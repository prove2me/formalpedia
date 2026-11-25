-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:37.493023+00:00
-- url     : https://prove2.me/theorems/14469ef9-7fab-52bd-82e3-bb328fd5e588
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib Gen deh z Of   e42b9125a01b: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib Gen deh z Of   e42b9125a01b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib Gen deh z Of   e42b9125a01b construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib Gen deh z Of   e42b9125a01b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L176-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L176-L194

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
variable [DecidableEq ι] (G : Gen x e) {w : Fin (D + 1) → ℂ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b (hw : G.Good w) {ρ : ℂ} (hρ : G.P.eval₂ (deh w 0) ρ = 0) :
    deh (G.zOf w ρ) (e 0) G.Θ = ρ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«Gen».«deh_zOf_Θ» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_Gen_deh_zOf___e42b9125a01b
