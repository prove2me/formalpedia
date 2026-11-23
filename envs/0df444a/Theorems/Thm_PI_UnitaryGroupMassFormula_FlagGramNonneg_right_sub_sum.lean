-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_right_sub_sum
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.right_sub_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:17.178804+00:00
-- url     : https://prove2.me/theorems/a526a7d0-0fd1-4345-ac30-1a388619d235
-- title:
--   Flag Gram Nonneg: right sub sum
-- statement:
--   The Flag Gram Nonneg construction uses the right sub sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L54-L57

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.right_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT x (z - ∑ a, c a • f a) = hT x z - ∑ a, c a * hT x (f a) := by sorry
