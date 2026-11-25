-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:19:00.021956+00:00
-- url     : https://prove2.me/theorems/ce4184e6-5992-42fe-b73c-9aca327db722
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Matrix Sub Degree log gram Det d03f3f69f313: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Matrix Sub Degree log gram Det d03f3f69f313 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Matrix Sub Degree log gram Det d03f3f69f313 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CardQuotientEqGenIndex.lean#L83-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CardQuotientEqGenIndex.lean#L83-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex
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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313 {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) (v : Fin r → M)
    (hv : ∀ i, (v i : Fin N → K) = c • u i) (σ : K →+* ℂ) :
    Real.log (gramDet (matrixBundle M H hH hconj).metric σ v) =
      r * (2 * Real.log ‖σ c‖) + Real.log (gramAt (H σ) σ u).det.re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«MatrixSubDegree».«log_gramDet» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313
