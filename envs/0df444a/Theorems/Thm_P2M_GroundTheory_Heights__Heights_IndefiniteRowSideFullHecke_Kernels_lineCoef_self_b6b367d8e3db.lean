-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_self_b6b367d8e3db
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_self_b6b367d8e3db
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:21.429174+00:00
-- url     : https://prove2.me/theorems/89d65ce8-518e-463c-a08d-404d2ef777e4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef self b6b367d8e3db: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef self b6b367
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef self b6b367d8e3db construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef self b6b367d8e3db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L87-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}
variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_self_b6b367d8e3db : lineCoef hN hl hl0 ⟨l, hl⟩ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«lineCoef_self» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_self_b6b367d8e3db
