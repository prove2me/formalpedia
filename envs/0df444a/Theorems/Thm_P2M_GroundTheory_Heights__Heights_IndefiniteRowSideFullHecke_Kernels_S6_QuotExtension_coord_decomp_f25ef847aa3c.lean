-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:16.328189+00:00
-- url     : https://prove2.me/theorems/df65a11f-8c00-43de-bf45-4a08521f712b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension coord decomp f25ef847aa3c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Qu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension coord decomp f25ef847aa3c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension coord decomp f25ef847aa3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L87-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L87-L120

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n)
    (σ : K →+* ℂ) (x : Fibre σ (idealLattice a)) :
    ∃ β : Fin m → ℂ, latticeCoord σ (idealLattice a) x =
      embMat σ (Sum.elim b c) *ᵥ Sum.elim β (latticeCoord σ (quotLattice a b c hli hmk)
        ((quotProj a b c hli hmk).lTensor (ComplexAt σ) x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«QuotExtension».«coord_decomp» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c
