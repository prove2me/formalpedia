-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9
-- name    : P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:49.08875+00:00
-- url     : https://prove2.me/theorems/6f4f520f-bcca-4734-8dbe-dd851ff1d4bb
-- title:
--   P2 M Ground Theory Heights  Heights Model eq zero of coprime mul eq zero aedbac591ad9: P2 M Ground Theory Heights  Heights Model eq zero of coprime mul eq zero aedbac591ad9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model eq zero of coprime mul eq zero aedbac591ad9 construction uses the P2 M Ground Theory Heights  Heights Model eq zero of coprime mul eq zero aedbac591ad9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PLocSectionsInj.lean#L24-L45

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

theorem P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9 {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : ℕ) (hp : p.Prime) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ ((ordCompl[p] N : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (s : Γ(X, W))
    (hs : (u : Γ(X, W)) * s = 0) : s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«eq_zero_of_coprime_mul_eq_zero» := P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9
