-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_two_package_4ea384e90e84
-- name    : P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_two_package_4ea384e90e84
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:00.96044+00:00
-- url     : https://prove2.me/theorems/be17a1ea-c012-5f8a-ae9a-5613842a965b
-- title:
--   P2 M Formalism L2 Indef Examples  quadratic example rank two package 4ea384e90e84: P2 M Formalism L2 Indef Examples  quadratic example rank two package 4ea384e90e84
-- statement:
--   The P2 M Formalism L2 Indef Examples  quadratic example rank two package 4ea384e90e84 construction uses the P2 M Formalism L2 Indef Examples  quadratic example rank two package 4ea384e90e84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L817-L819
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean#L817-L819

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

theorem P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_two_package_4ea384e90e84 (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) (C CH : ℝ) :
    (two.df K3 v0).WF ∧ Nonempty (IndefPkg (faceTwo v0 w).A (faceTwo v0 w).fc C CH) := by sorry

alias «Formalism».«L2».«Indef».«Examples₂».«quadratic_example_rank_two_package» := P2M_Formalism_L2_Indef_Examples__quadratic_example_rank_two_package_4ea384e90e84
