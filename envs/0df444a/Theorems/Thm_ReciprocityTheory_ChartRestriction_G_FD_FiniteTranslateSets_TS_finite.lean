-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FiniteTranslateSets_TS_finite
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.TS_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:38.902391+00:00
-- url     : https://prove2.me/theorems/443a0621-9425-562b-92f2-d27a4690c28d
-- title:
--   Finite Translate Sets: TS finite
-- statement:
--   The Finite Translate Sets construction uses the TS finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L49-L57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FiniteTranslateSets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets
open NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.TS_finite (R T : ℝ) (hR : 0 ≤ R) : (TS X (ι := ι) R T).Finite := by sorry
