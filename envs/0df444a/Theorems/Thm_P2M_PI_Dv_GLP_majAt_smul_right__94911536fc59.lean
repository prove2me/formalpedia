-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59
-- name    : P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:42.68696+00:00
-- url     : https://prove2.me/theorems/e7bb282b-8c8f-42f7-9e95-80da472870b6
-- title:
--   P2 M PI Dv GLP maj At smul right  94911536fc59: P2 M PI Dv GLP maj At smul right  94911536fc59
-- statement:
--   The P2 M PI Dv GLP maj At smul right  94911536fc59 construction uses the P2 M PI Dv GLP maj At smul right  94911536fc59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L46-L52

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

theorem P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59 (c : K) (x y : V) :
    majAt b X v x (c • y) = v.embedding c * majAt b X v x y := by sorry

alias «PI».«Dv».«GLP».«majAt_smul_right'» := P2M_PI_Dv_GLP_majAt_smul_right__94911536fc59
