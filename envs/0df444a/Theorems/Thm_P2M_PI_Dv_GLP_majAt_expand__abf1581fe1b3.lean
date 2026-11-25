-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3
-- name    : P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:03.842866+00:00
-- url     : https://prove2.me/theorems/f7a6974a-b931-446f-82e4-1eea9d7b04bf
-- title:
--   P2 M PI Dv GLP maj At expand  abf1581fe1b3: P2 M PI Dv GLP maj At expand  abf1581fe1b3
-- statement:
--   The P2 M PI Dv GLP maj At expand  abf1581fe1b3 construction uses the P2 M PI Dv GLP maj At expand  abf1581fe1b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L75-L81

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

theorem P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3 (c : K) (u w : V) :
    majAt b X v (u + c • w) (u + c • w) = majAt b X v u u + v.embedding c * majAt b X v u w +
      star (v.embedding c) * star (majAt b X v u w) +
      star (v.embedding c) * v.embedding c * majAt b X v w w := by sorry

alias «PI».«Dv».«GLP».«majAt_expand'» := P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3
