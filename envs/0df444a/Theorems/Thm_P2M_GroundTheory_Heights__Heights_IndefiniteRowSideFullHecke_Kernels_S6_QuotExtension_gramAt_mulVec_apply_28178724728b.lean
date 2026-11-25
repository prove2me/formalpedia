-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:54.575609+00:00
-- url     : https://prove2.me/theorems/8408282f-8afe-4d56-a9ac-93c8c9e74508
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At mul Vec apply 28178724728b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kern
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At mul Vec apply 28178724728b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At mul Vec apply 28178724728b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L63-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
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
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] (u : ι → Fin n → K) (w : ι → ℂ) (s : ι) :
    (gramAt h σ u *ᵥ w) s = star (embVec σ (u s)) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«QuotExtension».«gramAt_mulVec_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b
