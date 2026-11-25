-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:28.714504+00:00
-- url     : https://prove2.me/theorems/a5dbb80b-bd6d-5331-aa17-ba261a150a1a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane line Index smul f78a06c73a31: P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane line Index smul f78a06c73a31
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane line Index smul f78a06c73a31 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gaussian Plane line Index smul f78a06c73a31 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Examples.lean#L17-L44

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31 {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GaussianPlane».«lineIndex_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GaussianPlane_lineIndex_smul_f78a06c73a31
