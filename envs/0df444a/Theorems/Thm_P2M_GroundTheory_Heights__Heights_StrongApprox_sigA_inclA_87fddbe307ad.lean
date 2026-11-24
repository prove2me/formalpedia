-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:25.702808+00:00
-- url     : https://prove2.me/theorems/adfe9ecc-6dc2-4427-9d12-090ad8573f16
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx sig A incl A 87fddbe307ad: P2 M Ground Theory Heights  Heights Strong Approx sig A incl A 87fddbe307ad
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx sig A incl A 87fddbe307ad construction uses the P2 M Ground Theory Heights  Heights Strong Approx sig A incl A 87fddbe307ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L354-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L354-L356

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad (x : GaussQ) :
    sigA (conj ℚ GaussQ) (inclA ℚ GaussQ x) = inclA ℚ GaussQ (conj ℚ GaussQ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«sigA_inclA» := P2M_GroundTheory_Heights__Heights_StrongApprox_sigA_inclA_87fddbe307ad
