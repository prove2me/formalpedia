-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_zero_5d407d771e30
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_zero_5d407d771e30
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:31.621162+00:00
-- url     : https://prove2.me/theorems/95fa672e-fade-4e2e-8f71-68429455f408
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef eq zero 5d407d771e30: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef eq zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef eq zero 5d407d771e30 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels line Coef eq zero 5d407d771e30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L91-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L91-L99

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_zero_5d407d771e30 {w : N} (hw : lineCoef hN hl hl0 w = 0) : (w : E.carrier) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«lineCoef_eq_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_zero_5d407d771e30
