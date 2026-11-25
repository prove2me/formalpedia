-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisHomeo_apply_9d3b6d544422
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisHomeo_apply_9d3b6d544422
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:16.041601+00:00
-- url     : https://prove2.me/theorems/dddf53cc-8413-5661-b333-cee5e9921d01
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Homeo apply 9d3b6d544422: P2 M Ground Theory Heights  Heights Finite Covolume heis Homeo apply 9d3b6d544422
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Homeo apply 9d3b6d544422 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Homeo apply 9d3b6d544422 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L120-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusHomeo
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
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisHomeo_apply_9d3b6d544422 (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀) :
    heisHomeo hp p = heisPoint hp p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisHomeo_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisHomeo_apply_9d3b6d544422
