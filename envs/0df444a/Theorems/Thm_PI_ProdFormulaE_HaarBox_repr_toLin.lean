-- Prove2me | Theorems.Thm_PI_ProdFormulaE_HaarBox_repr_toLin
-- name    : PI.ProdFormulaE.HaarBox.repr_toLin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:36:07.964499+00:00
-- url     : https://prove2.me/theorems/24fa4066-168c-58aa-b31d-328a044d85b6
-- title:
--   Haar Box: repr to Lin
-- statement:
--   The Haar Box construction uses the repr to Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarTransv.lean#L14-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem PI.ProdFormulaE.HaarBox.repr_toLin (b : Basis ι K E) (A : Matrix ι ι K) (x : E) :
    b.repr (Matrix.toLin b b A x) = A *ᵥ b.repr x := by sorry
