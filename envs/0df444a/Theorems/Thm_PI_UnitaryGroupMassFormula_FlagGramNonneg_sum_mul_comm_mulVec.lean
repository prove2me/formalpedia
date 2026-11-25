-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_sum_mul_comm_mulVec
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.sum_mul_comm_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:38:21.675679+00:00
-- url     : https://prove2.me/theorems/0b426046-bfc4-4d86-b669-07c85fa6b927
-- title:
--   Flag Gram Nonneg: sum mul comm mul Vec
-- statement:
--   The Flag Gram Nonneg construction uses the sum mul comm mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L34-L37

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.sum_mul_comm_mulVec {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ b, w b * A c b = (A *ᵥ w) c := by sorry
