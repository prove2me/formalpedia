-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:31:09.104362+00:00
-- url     : https://prove2.me/theorems/76a7526c-8973-4e86-8351-0934137c712e
-- title:
--   P2 M Ground Theory Heights  Heights Model exists coprime mul eq zero 4a4cdbd8cee2: P2 M Ground Theory Heights  Heights Model exists coprime mul eq zero 4a4cdbd8cee2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists coprime mul eq zero 4a4cdbd8cee2 construction uses the P2 M Ground Theory Heights  Heights Model exists coprime mul eq zero 4a4cdbd8cee2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L60-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L60-L97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2 {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) {V : X.Opens}
    (hV : IsAffineOpen V) (s : Γ(X, V)) (hs : (baseChangeMap f (ZLoc p)).app V s = 0) :
    ∃ u : ℤ, ¬ ((p : ℕ) : ℤ) ∣ u ∧ (u : Γ(X, V)) * s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_coprime_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2
