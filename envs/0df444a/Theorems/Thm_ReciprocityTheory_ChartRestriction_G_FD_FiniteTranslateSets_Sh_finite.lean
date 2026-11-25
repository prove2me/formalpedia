-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FiniteTranslateSets_Sh_finite
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sh_finite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:35.598411+00:00
-- url     : https://prove2.me/theorems/8ab66329-2e03-5e6c-a019-3b66fb601688
-- title:
--   Finite Translate Sets: Sh finite
-- statement:
--   The Finite Translate Sets construction uses the Sh finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L15-L23

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sh_finite (R : ℝ) (hR : 0 ≤ R) : (Sh X R).Finite := by sorry
