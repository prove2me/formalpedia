-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_uq_kSpan_stable
-- name    : ReciprocityTheory.ChartRestriction.DS.HW.uq_kSpan_stable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:33:52.806466+00:00
-- url     : https://prove2.me/theorems/54eb208d-8eb1-455d-9751-cb4be02971ac
-- title:
--   HW: uq k Span stable
-- statement:
--   The HW construction uses the uq k Span stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/UniqueA.lean#L25-L29

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V)

theorem ReciprocityTheory.ChartRestriction.DS.HW.uq_kSpan_stable (x : V) : KStable ε F (kSpan ε F x) := by sorry
