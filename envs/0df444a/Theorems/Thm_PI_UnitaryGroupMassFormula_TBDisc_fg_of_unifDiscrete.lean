-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_fg_of_unifDiscrete
-- name    : PI.UnitaryGroupMassFormula.TBDisc.fg_of_unifDiscrete
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:28.138077+00:00
-- url     : https://prove2.me/theorems/ea1d7b53-53ba-4437-bd84-e04fbc31ee32
-- title:
--   TBDisc: fg of unif Discrete
-- statement:
--   The TBDisc construction uses the fg of unif Discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L65-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L65-L116

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

theorem PI.UnitaryGroupMassFormula.TBDisc.fg_of_unifDiscrete [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nf : NormFam K V)
    (M : Submodule (𝓞 K) V) (hM : UnifDiscrete Nf M) : M.FG := by sorry
