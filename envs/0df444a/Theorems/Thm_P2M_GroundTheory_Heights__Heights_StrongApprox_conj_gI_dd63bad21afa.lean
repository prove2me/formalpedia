-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa
-- name    : P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:58.360545+00:00
-- url     : https://prove2.me/theorems/1a068d3b-7e08-4680-a868-18955e35f0cf
-- title:
--   P2 M Ground Theory Heights  Heights Strong Approx conj g I dd63bad21afa: P2 M Ground Theory Heights  Heights Strong Approx conj g I dd63bad21afa
-- statement:
--   The P2 M Ground Theory Heights  Heights Strong Approx conj g I dd63bad21afa construction uses the P2 M Ground Theory Heights  Heights Strong Approx conj g I dd63bad21afa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L283-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StrongApproximation/Statements.lean#L283-L284

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

theorem P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa : conj ℚ GaussQ gI = -gI := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StrongApprox».«conj_gI» := P2M_GroundTheory_Heights__Heights_StrongApprox_conj_gI_dd63bad21afa
