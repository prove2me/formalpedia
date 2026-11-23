-- Prove2me | Theorems.Thm_PI_Dv_ProjGramW_span_O_famC
-- name    : PI.Dv.ProjGramW.span_O_famC
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:11.797745+00:00
-- url     : https://prove2.me/theorems/eddf6712-4766-4098-a7d9-aeb24b6ed752
-- title:
--   Proj Gram W: span O fam C
-- statement:
--   The Proj Gram W construction uses the span O fam C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionGramMatrices/IdxDet.lean#L50-L53

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

theorem PI.Dv.ProjGramW.span_O_famC {d : ℕ} (b : Fin d → V) (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC b C)) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K ((Submodule.span (𝓞 K) (Set.range b) : Submodule (𝓞 K) V) : Set V) := by sorry
