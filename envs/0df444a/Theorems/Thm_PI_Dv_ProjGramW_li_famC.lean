-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_li_famC
-- name    : PI.Dv.ProjGramW.li_famC
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:50.179696+00:00
-- url     : https://prove2.me/theorems/c0eb03ec-fddd-5be5-a700-1e6a8ebf2e2e
-- title:
--   Proj Gram W: li fam C
-- statement:
--   The Proj Gram W construction uses the li fam C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L144-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L144-L145

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.Dv.ProjGramW.li_famC {d : ℕ} {b : Fin d → V} (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : LinearIndependent K (famC b C) := by sorry
