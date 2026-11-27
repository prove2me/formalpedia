-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_intAt_9cde473eb65e
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_intAt_9cde473eb65e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:29.782376+00:00
-- url     : https://prove2.me/theorems/a895a7c0-b78c-448a-abb1-a108564271a9
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx one mem int At 9cde473eb65e: P2 M Ground Theory Heights  Heights Strong Approx one mem int At 9cde473eb65e
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx one mem int At 9cde473eb65e construction uses the P2 M Ground Theory Heights  Heights Strong Approx one mem int At 9cde473eb65e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L377-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L377-L378

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA
open QuadraticAlgebra GroundTheory.Heights₂.Theta GroundTheory.Automorphic
attribute [local instance] topAE
attribute [local instance] isModuleTopology_AE

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_intAt_9cde473eb65e : (1 : Kv GaussQ v5) ∈ intAt GaussQ v5 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«one_mem_intAt» := P2M_GroundTheory_Heights__Heights_StrongApprox_one_mem_intAt_9cde473eb65e
