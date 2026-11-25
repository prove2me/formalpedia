-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a
-- name    : P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:10.934188+00:00
-- url     : https://prove2.me/theorems/073f8e8f-a0d0-4523-b68d-570f243aa64d
-- title:
--   P2 M Ground Theory Heights  Heights Root Point Conjugation map minor 86bd49ff7f1a: P2 M Ground Theory Heights  Heights Root Point Conjugation map minor 86bd49ff7f1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Point Conjugation map minor 86bd49ff7f1a construction uses the P2 M Ground Theory Heights  Heights Root Point Conjugation map minor 86bd49ff7f1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L93-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L93-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootPointConjugation

theorem P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {j m : ℕ}
    (Z : Matrix (Fin j) (Fin m) R) (I : PlIdx j m) :
    φ (colsOf (onePipe Z) I).det = (colsOf (onePipe (Z.map φ)) I).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointConjugation».«map_minor» := P2M_GroundTheory_Heights__Heights_RootPointConjugation_map_minor_86bd49ff7f1a
