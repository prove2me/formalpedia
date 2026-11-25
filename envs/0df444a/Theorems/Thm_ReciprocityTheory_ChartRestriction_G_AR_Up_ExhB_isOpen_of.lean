-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_isOpen_of
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.isOpen_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:56:16.896822+00:00
-- url     : https://prove2.me/theorems/391f2ce1-8e8b-4ca7-9d67-1928eca29208
-- title:
--   Exh B: is Open of
-- statement:
--   The Exh B construction uses the is Open of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfA.lean#L111-L116

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.isOpen_of {X : Type*} [TopologicalSpace X] {f p q : ℕ} (g : X → V (nD f p q))
    (hg : ∀ i, Continuous fun x => g x i) :
    IsOpen {x | ∀ k, (1 - Zof (g x) k * (Zof (g x) k)ᴴ).PosDef} := by sorry
