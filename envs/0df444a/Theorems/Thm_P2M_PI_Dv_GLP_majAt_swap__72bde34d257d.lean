-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_swap__72bde34d257d
-- name    : P2M_PI_Dv_GLP_majAt_swap__72bde34d257d
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:18.784318+00:00
-- url     : https://prove2.me/theorems/aa69cb79-0795-43f3-ab9a-7df994c77e1f
-- title:
--   P2 M PI Dv GLP maj At swap  72bde34d257d: P2 M PI Dv GLP maj At swap  72bde34d257d
-- statement:
--   The P2 M PI Dv GLP maj At swap  72bde34d257d construction uses the P2 M PI Dv GLP maj At swap  72bde34d257d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L54-L58

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

theorem P2M_PI_Dv_GLP_majAt_swap__72bde34d257d (x y : V) : majAt b X v y x = star (majAt b X v x y) := by sorry

alias «PI».«Dv».«GLP».«majAt_swap'» := P2M_PI_Dv_GLP_majAt_swap__72bde34d257d
