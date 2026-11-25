-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormFormDvd_hypotheses_inhabited_dfc20cebb5be
-- name    : P2M_GroundTheory_Heights__Heights_NormFormDvd_hypotheses_inhabited_dfc20cebb5be
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:25.953802+00:00
-- url     : https://prove2.me/theorems/4883f518-41c0-4e69-ac04-e983ce3bddcd
-- title:
--   P2 M Ground Theory Heights  Heights Norm Form Dvd hypotheses inhabited dfc20cebb5be: P2 M Ground Theory Heights  Heights Norm Form Dvd hypotheses inhabited dfc20cebb5be
-- statement:
--   The P2 M Ground Theory Heights  Heights Norm Form Dvd hypotheses inhabited dfc20cebb5be construction uses the P2 M Ground Theory Heights  Heights Norm Form Dvd hypotheses inhabited dfc20cebb5be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsNormForm.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsNormForm.lean#L54-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NormFormDvd_hypotheses_inhabited_dfc20cebb5be :
    Algebra.adjoin ℚ (Set.range (fun _ : Fin 1 => (1 : ℚ))) = ⊤ ∧
      ∑ m : Fin 1, (fun _ : Fin 1 => (1 : ℚ)) m • (fun _ : Fin 1 => (1 : ℚ)) m = 1 ∧
      (∑ m : Fin 1, X m * C ((fun _ : Fin 1 => (1 : ℚ)) m)) ∣
        map (algebraMap ℚ ℚ) (X 0 : MvPolynomial (Fin 1) ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormFormDvd».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_NormFormDvd_hypotheses_inhabited_dfc20cebb5be
