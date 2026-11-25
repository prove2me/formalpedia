-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PG_eval_lineHom
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:59:12.591445+00:00
-- url     : https://prove2.me/theorems/79c8c218-dd1f-49e2-ab3b-5be18839ffbc
-- title:
--   PG: eval line Hom
-- statement:
--   The PG construction uses the eval line Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PolyGrowthStatementPfB.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PolyGrowthStatementPfB.lean#L13-L20

import Mathlib
import Definitions.Def_Lemmata_CofiniteContinuousBounds_LeOfCofinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PG
open MvPolynomial
variable {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PG.eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by sorry
