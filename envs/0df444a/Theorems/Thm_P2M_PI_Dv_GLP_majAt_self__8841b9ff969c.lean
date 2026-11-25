-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_self__8841b9ff969c
-- name    : P2M_PI_Dv_GLP_majAt_self__8841b9ff969c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:10.570843+00:00
-- url     : https://prove2.me/theorems/e9e6e7b9-1de4-411c-8f8d-ca4ea4168494
-- title:
--   P2 M PI Dv GLP maj At self  8841b9ff969c: P2 M PI Dv GLP maj At self  8841b9ff969c
-- statement:
--   The P2 M PI Dv GLP maj At self  8841b9ff969c construction uses the P2 M PI Dv GLP maj At self  8841b9ff969c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L60-L65

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem P2M_PI_Dv_GLP_majAt_self__8841b9ff969c (x : V) : majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by sorry

alias «PI».«Dv».«GLP».«majAt_self'» := P2M_PI_Dv_GLP_majAt_self__8841b9ff969c
