-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd
-- name    : P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:24.17671+00:00
-- url     : https://prove2.me/theorems/5ce18a7c-2c10-49e2-8333-cc30535e820e
-- title:
--   P2 M PI Dv GLP fcoord smul  42bb95b005bd: P2 M PI Dv GLP fcoord smul  42bb95b005bd
-- statement:
--   The P2 M PI Dv GLP fcoord smul  42bb95b005bd construction uses the P2 M PI Dv GLP fcoord smul  42bb95b005bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L14-L19

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

theorem P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd (c : K) (x : V) : fcoord b X v (c • x) = v.embedding c • fcoord b X v x := by sorry

alias «PI».«Dv».«GLP».«fcoord_smul'» := P2M_PI_Dv_GLP_fcoord_smul__42bb95b005bd
