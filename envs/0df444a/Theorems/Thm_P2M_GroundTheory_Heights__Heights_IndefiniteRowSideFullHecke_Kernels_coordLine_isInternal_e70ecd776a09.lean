-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLine_isInternal_e70ecd776a09
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLine_isInternal_e70ecd776a09
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:52:23.497232+00:00
-- url     : https://prove2.me/theorems/e32d0d96-9e90-441d-b322-4acbaedeea46
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Line is Internal e70ecd776a09: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Line is
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Line is Internal e70ecd776a09 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels coord Line is Internal e70ecd776a09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L45-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L45-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_SingleMemIdealLattice
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
open scoped nonZeroDivisors
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLine_isInternal_e70ecd776a09 {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    DirectSum.IsInternal (coordLine a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«coordLine_isInternal» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLine_isInternal_e70ecd776a09
