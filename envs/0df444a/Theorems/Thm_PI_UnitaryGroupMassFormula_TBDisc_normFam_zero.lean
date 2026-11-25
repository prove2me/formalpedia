-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_normFam_zero
-- name    : PI.UnitaryGroupMassFormula.TBDisc.normFam_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:14.79956+00:00
-- url     : https://prove2.me/theorems/fe9e8eba-b1a2-4ae1-b910-4ab6f9c460dd
-- title:
--   TBDisc: norm Fam zero
-- statement:
--   The TBDisc construction uses the norm Fam zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L30-L32

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

theorem PI.UnitaryGroupMassFormula.TBDisc.normFam_zero (Nf : NormFam K V) (σ : K →+* ℂ) : Nf.N σ 0 = 0 := by sorry
