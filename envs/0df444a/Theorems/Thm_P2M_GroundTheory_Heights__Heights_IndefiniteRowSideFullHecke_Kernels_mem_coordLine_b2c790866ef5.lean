-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:38.345281+00:00
-- url     : https://prove2.me/theorems/49a55074-745d-5cbf-a682-c9300bf03789
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels mem coord Line b2c790866ef5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels mem coord Line b2c790
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels mem coord Line b2c790866ef5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels mem coord Line b2c790866ef5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/SingleMemIdealLattice.lean#L19-L31

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5 {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} {x : Fin n}
    {w : idealLattice a} : w ∈ coordLine a x ↔ ∀ y, y ≠ x → (w : Fin n → K) y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«mem_coordLine» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_mem_coordLine_b2c790866ef5
