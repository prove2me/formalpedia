-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisConjLin_apply_aa93a34fa3c4
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisConjLin_apply_aa93a34fa3c4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:14.928124+00:00
-- url     : https://prove2.me/theorems/efc077e6-1b24-5154-90b2-2c330e7cd5a2
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Conj Lin apply aa93a34fa3c4: P2 M Ground Theory Heights  Heights Finite Covolume heis Conj Lin apply aa93a34fa3c4
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Conj Lin apply aa93a34fa3c4 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Conj Lin apply aa93a34fa3c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusHomeo.lean#L158-L161

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
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisConjLin_apply_aa93a34fa3c4 (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y : heisY h v x₀ w₀) (w : InfinitePlace E) :
    ((heisConjLin g hg y : heisY h v x₀ w₀) : InfinitePlace E → ι → ℂ) w =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ (y : InfinitePlace E → ι → ℂ) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisConjLin_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisConjLin_apply_aa93a34fa3c4
