-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_left_sub_sum
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.left_sub_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:14.87054+00:00
-- url     : https://prove2.me/theorems/9f91ed20-4324-4f7e-8804-12f6132a785b
-- title:
--   Flag Gram Nonneg: left sub sum
-- statement:
--   The Flag Gram Nonneg construction uses the left sub sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L48-L52

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_SumMulCommMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.left_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT (z - ∑ a, c a • f a) x = hT z x - ∑ a, star (c a) * hT (f a) x := by sorry
