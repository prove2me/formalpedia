-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0
-- name    : P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:36:59.192824+00:00
-- url     : https://prove2.me/theorems/1022f2ca-94e8-4527-944b-099efa7119c4
-- title:
--   P2 M Ground Theory Heights  Heights Root Point Conjugation entry eq minor a8075f6b6ae0: P2 M Ground Theory Heights  Heights Root Point Conjugation entry eq minor a8075f6b6ae0
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Point Conjugation entry eq minor a8075f6b6ae0 construction uses the P2 M Ground Theory Heights  Heights Root Point Conjugation entry eq minor a8075f6b6ae0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L71-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean#L71-L91

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

theorem P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0 {j m : ℕ} (a : Fin j) (b : Fin m) :
    ∃ s : ℤ, ∀ (R : Type) [CommRing R] (Z : Matrix (Fin j) (Fin m) R),
      Z a b = s * (colsOf (onePipe Z) (idxAB a b)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootPointConjugation».«entry_eq_minor» := P2M_GroundTheory_Heights__Heights_RootPointConjugation_entry_eq_minor_a8075f6b6ae0
