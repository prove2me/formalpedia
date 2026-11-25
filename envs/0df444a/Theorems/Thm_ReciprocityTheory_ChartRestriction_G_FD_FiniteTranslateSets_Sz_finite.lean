-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FiniteTranslateSets_Sz_finite
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sz_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:34.926178+00:00
-- url     : https://prove2.me/theorems/16dcb55d-865e-58a8-aac2-bf6c12d5980b
-- title:
--   Finite Translate Sets: Sz finite
-- statement:
--   The Finite Translate Sets construction uses the Sz finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FiniteTranslateSets.lean#L27-L41

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

theorem ReciprocityTheory.ChartRestriction.G.FD.FiniteTranslateSets.Sz_finite (T : ℝ) : (Sz T).Finite := by sorry
