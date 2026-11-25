-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:35.522193+00:00
-- url     : https://prove2.me/theorems/ad61da37-610a-43bd-a014-5d470a26f04e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume vec At injective 5e91e8c6ade2: P2 M Ground Theory Heights  Heights Finite Covolume vec At injective 5e91e8c6ade2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume vec At injective 5e91e8c6ade2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume vec At injective 5e91e8c6ade2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PScalingLaw.lean#L75-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2 (v : Basis ι E W) : Function.Injective (vecAt v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«vecAt_injective» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
