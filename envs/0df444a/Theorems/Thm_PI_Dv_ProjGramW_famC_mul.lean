-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_famC_mul
-- name    : PI.Dv.ProjGramW.famC_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:27.257951+00:00
-- url     : https://prove2.me/theorems/ee437f69-42c7-457e-806b-ef530ed2e163
-- title:
--   Proj Gram W: fam C mul
-- statement:
--   The Proj Gram W construction uses the fam C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L18-L26

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

theorem PI.Dv.ProjGramW.famC_mul {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C C' : Matrix (Fin d) (Fin d) K) : famC (famC b C) C' = famC b (C * C') := by sorry
