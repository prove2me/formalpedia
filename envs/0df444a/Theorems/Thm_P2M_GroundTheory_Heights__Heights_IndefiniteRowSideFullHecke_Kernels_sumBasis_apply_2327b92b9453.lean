-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:26:09.387987+00:00
-- url     : https://prove2.me/theorems/5c0bcb1b-72e0-571d-b774-1f3809aa3c42
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels sum Basis apply 2327b92b9453: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels sum Basis apply 2327
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels sum Basis apply 2327b92b9453 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels sum Basis apply 2327b92b9453 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean#L205-L208

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
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
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453 {n m k : ℕ} (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
    (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) (i : Fin m ⊕ Fin k) :
    sumBasis b c hli hmk i = Sum.elim b c i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«sumBasis_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
