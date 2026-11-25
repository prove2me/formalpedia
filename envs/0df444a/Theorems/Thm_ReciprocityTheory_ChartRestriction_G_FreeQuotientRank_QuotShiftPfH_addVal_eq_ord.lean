-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_QuotShiftPfH_addVal_eq_ord
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH.addVal_eq_ord
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:22.897716+00:00
-- url     : https://prove2.me/theorems/2827f0a7-b39a-5872-8413-d3a71f96ab03
-- title:
--   Quot Shift Pf H: add Val eq ord
-- statement:
--   The Quot Shift Pf H construction uses the add Val eq ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QuotShiftPfH.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QuotShiftPfH.lean#L120-L125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPfH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH.addVal_eq_ord (x : Rv F v) (hx : (x : F) ≠ 0) :
    IsDiscreteValuationRing.addVal (Rv F v) x = ((ordAt v (x : F)).toNat : ℕ∞) := by sorry
