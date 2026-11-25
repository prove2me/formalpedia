-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_image_a464d991008c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_image_a464d991008c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:53.484803+00:00
-- url     : https://prove2.me/theorems/546bb7e7-ec67-48f2-8b86-6ba7181ca55c
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above image a464d991008c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above image a464d991
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above image a464d991008c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close bdd Above image a464d991008c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/RenameBlockIsWeightedHomogeneous.lean#L216-L219

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_image_a464d991008c (P : ArithVariety n) (k₀ : ι) {N : ℕ}
    {f : MvPolynomial (Fin (n k₀ + 1)) ℤ} (hf : f.IsHomogeneous N) :
    BddAbove ((fun w ↦ ‖eval₂ (Int.castRingHom ℂ) w f‖ / l2Norm w ^ N) '' oneBlockPoints P k₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«bddAbove_image» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_bddAbove_image_a464d991008c
