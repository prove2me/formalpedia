-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_sum_sign_prod_ind_23f326540616
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_sum_sign_prod_ind_23f326540616
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:37:09.578017+00:00
-- url     : https://prove2.me/theorems/6e2b8b3a-1e25-5cbb-901a-2269e8ca745e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual sum sign prod ind 23f326540616: P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual sum sign prod ind 23f326540616
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual sum sign prod ind 23f326540616 construction uses the P2 M Ground Theory Heights  Heights Kleiman Inter Num Eventual sum sign prod ind 23f326540616 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PInterNumEventual.lean#L21-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PRestrLenEuler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumEventual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumEventual

theorem P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_sum_sign_prod_ind_23f326540616 {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«InterNumEventual».«sum_sign_prod_ind» := P2M_GroundTheory_Heights__Heights_Kleiman_InterNumEventual_sum_sign_prod_ind_23f326540616
