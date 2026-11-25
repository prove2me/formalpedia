-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6
-- name    : P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:05.585675+00:00
-- url     : https://prove2.me/theorems/7dfb0757-ba6d-5813-9b85-e9c60370fae7
-- title:
--   P2 M Ground Theory Heights  Heights exists embedding of mul c069f2dba8a6: P2 M Ground Theory Heights  Heights exists embedding of mul c069f2dba8a6
-- statement:
--   The P2 M Ground Theory Heights  Heights exists embedding of mul c069f2dba8a6 construction uses the P2 M Ground Theory Heights  Heights exists embedding of mul c069f2dba8a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L119-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockPoints.lean#L119-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
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
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6 {m : ℕ} (L : (Fin m → K) → ℂ)
    (hadd : ∀ u v, L (u + v) = L u + L v)
    (hmul : ∀ (j j' : Fin m) (a b a' b' : K), a * b = a' * b' →
      L (Pi.single j a) * L (Pi.single j' b) = L (Pi.single j a') * L (Pi.single j' b'))
    (hne : ∃ v, L v ≠ 0) :
    ∃ (σ : K →+* ℂ) (w : Fin m → ℂ), w ≠ 0 ∧ ∀ v, L v = ∑ j, σ (v j) * w j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_embedding_of_mul» := P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6
