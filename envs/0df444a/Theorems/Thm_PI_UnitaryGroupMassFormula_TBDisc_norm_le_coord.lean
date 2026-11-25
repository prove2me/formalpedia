-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_norm_le_coord
-- name    : PI.UnitaryGroupMassFormula.TBDisc.norm_le_coord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:11.098807+00:00
-- url     : https://prove2.me/theorems/cf83798a-f5d3-5625-9661-0934007129ee
-- title:
--   TBDisc: norm le coord
-- statement:
--   The TBDisc construction uses the norm le coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L50-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L50-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

theorem PI.UnitaryGroupMassFormula.TBDisc.norm_le_coord (Nf : NormFam K V) (σ : K →+* ℂ) (v : V) :
    Nf.N σ v ≤ ‖coordMap (K := K) v‖ * ∑ i, Nf.N σ (Module.finBasis K V i) := by sorry
