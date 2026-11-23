-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_herm_one_sub
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.herm_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:28.219525+00:00
-- url     : https://prove2.me/theorems/e94bd943-7256-46d2-91df-bc321a565777
-- title:
--   Exh B: herm one sub
-- statement:
--   The Exh B construction uses the herm one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L101-L102

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.herm_one_sub {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) : (1 - Z * Zᴴ).IsHermitian := by sorry
