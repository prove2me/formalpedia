-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_mul_543a6845588e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_mul_543a6845588e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:06:16.787303+00:00
-- url     : https://prove2.me/theorems/206bb52e-7856-441a-9ffc-c8d38ec1f89f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Point mul 543a6845588e: P2 M Ground Theory Heights  Heights Finite Covolume heis Point mul 543a6845588e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Point mul 543a6845588e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Point mul 543a6845588e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L123-L133

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_mul_543a6845588e (hp : IsHyperbolicPair h x₀ w₀) (p q : HeisCoord h v x₀ w₀) :
    heisPoint hp p * heisPoint hp q = heisPoint hp (p.1 + q.1, p.2 + q.2 - fun w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((q.1 : InfinitePlace E → ι → ℂ) w)).im) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisPoint_mul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_mul_543a6845588e
