-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BlockSurjectivity_equiv_e333ad89fcd7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BlockSurjectivity_equiv_e333ad89fcd7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:15:25.507062+00:00
-- url     : https://prove2.me/theorems/361218a2-156f-5113-87f6-59d75440fca1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Block Surjectivity equiv e333ad89fcd7: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Block Surjectiv
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Block Surjectivity equiv e333ad89fcd7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Block Surjectivity equiv e333ad89fcd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemConePointsProjIdealIff.lean#L42-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemConePointsProjIdealIff.lean#L42-L69

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BlockSurjectivity_equiv_e333ad89fcd7 :
    GroundTheory.Heights₂.Heights.BlockSurjectivity.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BlockSurjectivity.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«BlockSurjectivity».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BlockSurjectivity_equiv_e333ad89fcd7
