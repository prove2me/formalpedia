-- Prove2me | Theorems.Thm_PI_WHw_eval_rowGen
-- name    : PI.WHw.eval_rowGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:12.629661+00:00
-- url     : https://prove2.me/theorems/4e716ed4-dfca-4c8a-a835-036540e5fbf8
-- title:
--   WHw: eval row Gen
-- statement:
--   The WHw construction uses the eval row Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HighestWeightIrreducible/ConstructionA.lean#L51-L60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WHw
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WHw.eval_rowGen {N n : ℕ} (a b : Fin N) (t : ℂ) (f : MvPolynomial (Fin N × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (1 + Matrix.single b a t) f := by sorry
