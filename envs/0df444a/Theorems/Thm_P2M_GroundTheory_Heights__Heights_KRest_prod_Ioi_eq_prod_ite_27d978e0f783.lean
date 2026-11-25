-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783
-- name    : P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:59.599716+00:00
-- url     : https://prove2.me/theorems/3776e093-47c0-4dee-ad9f-2a916c1dedea
-- title:
--   P2 M Ground Theory Heights  Heights KRest prod Ioi eq prod ite 27d978e0f783: P2 M Ground Theory Heights  Heights KRest prod Ioi eq prod ite 27d978e0f783
-- statement:
--   The P2 M Ground Theory Heights  Heights KRest prod Ioi eq prod ite 27d978e0f783 construction uses the P2 M Ground Theory Heights  Heights KRest prod Ioi eq prod ite 27d978e0f783 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/RestCutBasic.lean#L38-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic
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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783 {R : Type*} [CommMonoid R] {m : ℕ} (g : Fin m → Fin m → R) :
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, g i j =
      ∏ x : Fin m × Fin m, if x.1 < x.2 then g x.1 x.2 else 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KRest».«prod_Ioi_eq_prod_ite» := P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783
