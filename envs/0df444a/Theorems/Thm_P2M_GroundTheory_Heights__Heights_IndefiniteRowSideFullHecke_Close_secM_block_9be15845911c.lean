-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:25:14.065873+00:00
-- url     : https://prove2.me/theorems/03fd5d3b-1771-56eb-8b04-89272b3acf1e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sec M block 9be15845911c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sec M block 9be15845911c
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sec M block 9be15845911c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close sec M block 9be15845911c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L119-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L119-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
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
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c (P : ArithVariety n) (k₀ : ι) (N : ℕ) :
    secM (genPt P) (N • Pi.single k₀ 1) =
      (sec ℤ (fun i : Fin (n k₀ + 1) ↦ genPt P ⟨k₀, i⟩) N).toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«secM_block» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_secM_block_9be15845911c
