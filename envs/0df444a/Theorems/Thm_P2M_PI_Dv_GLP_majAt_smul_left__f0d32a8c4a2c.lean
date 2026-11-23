-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_smul_left__f0d32a8c4a2c
-- name    : P2M_PI_Dv_GLP_majAt_smul_left__f0d32a8c4a2c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:06.537178+00:00
-- url     : https://prove2.me/theorems/da8f890c-0994-4469-b343-04f136b21801
-- title:
--   P2 M PI Dv GLP maj At smul left  f0d32a8c4a2c: P2 M PI Dv GLP maj At smul left  f0d32a8c4a2c
-- statement:
--   The P2 M PI Dv GLP maj At smul left  f0d32a8c4a2c construction uses the P2 M PI Dv GLP maj At smul left  f0d32a8c4a2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L38-L44

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

theorem P2M_PI_Dv_GLP_majAt_smul_left__f0d32a8c4a2c (c : K) (x y : V) :
    majAt b X v (c • x) y = star (v.embedding c) * majAt b X v x y := by sorry

alias «PI».«Dv».«GLP».«majAt_smul_left'» := P2M_PI_Dv_GLP_majAt_smul_left__f0d32a8c4a2c
