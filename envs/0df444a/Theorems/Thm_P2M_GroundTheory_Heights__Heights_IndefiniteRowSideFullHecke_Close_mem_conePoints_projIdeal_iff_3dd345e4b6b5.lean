-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_projIdeal_iff_3dd345e4b6b5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_projIdeal_iff_3dd345e4b6b5
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:08.750898+00:00
-- url     : https://prove2.me/theorems/8b8ca3c8-cf6a-4fcb-b290-43c494e40bcc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points proj Ideal iff 3dd345e4b6b5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points proj Ideal iff 3dd345e4b6b5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close mem cone Points proj Ideal iff 3dd345e4b6b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemConePointsProjIdealIff.lean#L16-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemConePointsProjIdealIff.lean#L16-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemConePointsProjIdealIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_projIdeal_iff_3dd345e4b6b5 (P : ArithVariety n) (k₀ : ι)
    (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    w ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ ↔ w () ∈ oneBlockPoints P k₀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«mem_conePoints_projIdeal_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_mem_conePoints_projIdeal_iff_3dd345e4b6b5
