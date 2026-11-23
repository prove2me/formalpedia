-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_herm
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:02.46837+00:00
-- url     : https://prove2.me/theorems/a0e88771-f132-4e2b-8cb2-5890a4facda6
-- title:
--   Flag Gram Nonneg: herm
-- statement:
--   The Flag Gram Nonneg construction uses the herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/SumMulCommMulVec.lean#L43-L46

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

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.herm {hT : V →ₗ⋆[E] V →ₗ[E] E} (hS : hT.IsSymm) (x y : V) : hT x y = star (hT y x) := by sorry
