-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_majAt_selfadj__941a67e8f641
-- name    : P2M_PI_Dv_GLP_majAt_selfadj__941a67e8f641
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:55:51.107806+00:00
-- url     : https://prove2.me/theorems/2b06bca8-67ce-4dd1-86f9-47cbae66bf81
-- title:
--   P2 M PI Dv GLP maj At selfadj  941a67e8f641: P2 M PI Dv GLP maj At selfadj  941a67e8f641
-- statement:
--   The P2 M PI Dv GLP maj At selfadj  941a67e8f641 construction uses the P2 M PI Dv GLP maj At selfadj  941a67e8f641 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L125-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/MajAtZeroRight.lean#L125-L139

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

theorem P2M_PI_Dv_GLP_majAt_selfadj__941a67e8f641 [NumberField.IsTotallyComplex K] {G : Type} [Group G] [Fintype G]
    (ρ : Representation K G V) (hρ : ∀ g x, normAt b X v (ρ g x) = normAt b X v x)
    (a : G → K) (ha : ∀ g, star (v.embedding (a g)) = v.embedding (a g⁻¹)) (x y : V) :
    majAt b X v ((∑ g, a g • ρ g) x) y = majAt b X v x ((∑ g, a g • ρ g) y) := by sorry

alias «PI».«Dv».«GLP».«majAt_selfadj'» := P2M_PI_Dv_GLP_majAt_selfadj__941a67e8f641
