-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d
-- name    : P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:19.508878+00:00
-- url     : https://prove2.me/theorems/ca5d5d9b-297e-46ad-830d-825292482689
-- title:
--   P2 M Ground Theory Heights  Heights chart Section sup Norm LE aa7598e7119d: P2 M Ground Theory Heights  Heights chart Section sup Norm LE aa7598e7119d
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Section sup Norm LE aa7598e7119d construction uses the P2 M Ground Theory Heights  Heights chart Section sup Norm LE aa7598e7119d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Statements.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Statements.lean#L72-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d (P : ArithVariety n) (c0 : (k : ι) → Fin (n k + 1)) :
    (IntegralSection.chartSection P c0).SupNormLE (HermLine.standard n) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartSection_supNormLE» := P2M_GroundTheory_Heights__Heights_chartSection_supNormLE_aa7598e7119d
