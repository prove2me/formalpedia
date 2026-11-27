-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_BigA_projPerp_self
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:05.374241+00:00
-- url     : https://prove2.me/theorems/cd624bc2-ce1f-47a9-a2dd-6c9bb2fa2f2d
-- title:
--   Big A: proj Perp self
-- statement:
--   The Big A construction uses the proj Perp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfA.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/BigStatementPfA.lean#L10-L21

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BigStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.BigA
open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by sorry
