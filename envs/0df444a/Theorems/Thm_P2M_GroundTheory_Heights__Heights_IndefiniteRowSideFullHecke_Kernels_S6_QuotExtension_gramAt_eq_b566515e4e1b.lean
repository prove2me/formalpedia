-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:42:28.376878+00:00
-- url     : https://prove2.me/theorems/19abde70-c2f5-402b-9d07-11a98aaf8ca0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At eq b566515e4e1b: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At eq b566515e4e1b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Kernels S6 Quot Extension gram At eq b566515e4e1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulMemIdealLattice.lean#L45-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) : gramAt h σ u = (embMat σ u)ᴴ * h * embMat σ u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Kernels».«S6».«QuotExtension».«gramAt_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b
