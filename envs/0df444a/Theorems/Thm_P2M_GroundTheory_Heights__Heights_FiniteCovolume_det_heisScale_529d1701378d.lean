-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_heisScale_529d1701378d
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_heisScale_529d1701378d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:22:28.362752+00:00
-- url     : https://prove2.me/theorems/9d0e8d27-60a3-5f7e-90f7-e4d39dba86c8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume det heis Scale 529d1701378d: P2 M Ground Theory Heights  Heights Finite Covolume det heis Scale 529d1701378d
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume det heis Scale 529d1701378d construction uses the P2 M Ground Theory Heights  Heights Finite Covolume det heis Scale 529d1701378d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusDet.lean#L75-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusDet.lean#L75-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusCoords
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRadicalTorusModulusDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_heisScale_529d1701378d (hp : IsHyperbolicPair h x₀ w₀) (c : InfinitePlace E → ℂ) :
    LinearMap.det (heisScale h v x₀ w₀ c) =
      ∏ w, Complex.normSq (c w) ^ (Fintype.card ι - 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«det_heisScale» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_heisScale_529d1701378d
