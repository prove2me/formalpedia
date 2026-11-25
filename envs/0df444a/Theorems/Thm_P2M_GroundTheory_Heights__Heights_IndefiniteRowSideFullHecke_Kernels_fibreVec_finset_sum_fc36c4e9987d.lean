-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_finset_sum_fc36c4e9987d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_finset_sum_fc36c4e9987d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:35.976168+00:00
-- url     : https://prove2.me/theorems/d28d1621-ae9e-469b-8b9f-000b43309970
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels fibre Vec finset sum fc36c4e9987d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels fibre Vec finse
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels fibre Vec finset sum fc36c4e9987d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels fibre Vec finset sum fc36c4e9987d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean#L112-L115

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_finset_sum_fc36c4e9987d {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K} (σ : K →+* ℂ)
    {ι : Type*} (S : Finset ι) (f : ι → E.carrier) :
    fibreVec E.metric σ (∑ i ∈ S, f i) = ∑ i ∈ S, fibreVec E.metric σ (f i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«fibreVec_finset_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_finset_sum_fc36c4e9987d
