-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_one_package_97de2101beb0
-- name    : P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_one_package_97de2101beb0
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:18:02.814567+00:00
-- url     : https://prove2.me/theorems/2d2b0cce-1b25-5f82-a7ff-1f203a22fd8f
-- title:
--   P2 M Formalism L2 Indef Examples  quadratic example rank one package 97de2101beb0: P2 M Formalism L2 Indef Examples  quadratic example rank one package 97de2101beb0
-- statement:
--   The P2 M Formalism L2 Indef Examples  quadratic example rank one package 97de2101beb0 construction uses the P2 M Formalism L2 Indef Examples  quadratic example rank one package 97de2101beb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L798-L801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L798-L801

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open NumberField.IsCMField

theorem P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_one_package_97de2101beb0 (v0 : InfinitePlace K3) (C CH : ℝ) :
    (one.df K3 v0).WF ∧ Nonempty (IndefPkg (amb (one.base K3 v0))
      (fun _ => ⟨one.df K3 v0, one.df K3 v0, one.dc K3 v0, one.sp K3 v0, scaleOf (one.num K3 v0)⟩) C CH) := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«quadratic_example_rank_one_package» := P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_one_package_97de2101beb0
