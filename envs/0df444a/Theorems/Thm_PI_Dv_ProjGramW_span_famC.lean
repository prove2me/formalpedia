-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_span_famC
-- name    : PI.Dv.ProjGramW.span_famC
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:42.930926+00:00
-- url     : https://prove2.me/theorems/a34db4c8-bc80-4b4c-9573-f8f88696133a
-- title:
--   Proj Gram W: span fam C
-- statement:
--   The Proj Gram W construction uses the span fam C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L33-L46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]

theorem PI.Dv.ProjGramW.span_famC {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K (Set.range (famC b C)) = Submodule.span K (Set.range b) := by sorry
