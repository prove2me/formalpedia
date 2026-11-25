-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_placeScale_7f893252c050
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_placeScale_7f893252c050
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:22:03.749037+00:00
-- url     : https://prove2.me/theorems/7ba97c3d-6c2a-51cc-8de7-3d90718f1c41
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume det place Scale 7f893252c050: P2 M Ground Theory Heights  Heights Finite Covolume det place Scale 7f893252c050
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume det place Scale 7f893252c050 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume det place Scale 7f893252c050 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusDet.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PRadicalTorusModulusDet.lean#L109-L111

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
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_placeScale_7f893252c050 (r : InfinitePlace E → ℝ) : LinearMap.det (placeScale r) = ∏ w, r w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«det_placeScale» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_det_placeScale_7f893252c050
