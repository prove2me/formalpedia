-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uqG_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.uqG_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:41:22.186235+00:00
-- url     : https://prove2.me/theorems/1b1185b3-1c9b-5bbd-bc6a-e6f743079b1e
-- title:
--   HW: uq G apply
-- statement:
--   The HW construction uses the uq G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L61-L63

import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Formalism.REAL
variable {n : ℕ}
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem ReciprocityTheory.ChartRestriction.DS.HW.uqG_apply (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V') (a b : Fin n)
    (x : WithLp 2 (V × V')) :
    WithLp.ofLp (uqG F F' a b x) = (F a b (WithLp.ofLp x).1, F' a b (WithLp.ofLp x).2) := by sorry
