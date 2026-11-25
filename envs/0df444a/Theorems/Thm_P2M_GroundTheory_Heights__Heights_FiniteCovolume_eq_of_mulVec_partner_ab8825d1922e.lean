-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:41.988912+00:00
-- url     : https://prove2.me/theorems/3cc7179b-232b-4987-b623-5df328115288
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume eq of mul Vec partner ab8825d1922e: P2 M Ground Theory Heights  Heights Finite Covolume eq of mul Vec partner ab8825d1922e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume eq of mul Vec partner ab8825d1922e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume eq of mul Vec partner ab8825d1922e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L181-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L181-L204

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha
omit ha

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e {b : ι → ℂ} (hab : hForm H a b = 1) {n m : Matrix ι ι ℂ}
    (hn : nᴴ * H * n = H) (hm : mᴴ * H * m = H)
    (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a)
    (hm' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, m *ᵥ z = z + c • a) (hnb : n *ᵥ b = m *ᵥ b) :
    n = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«eq_of_mulVec_partner» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e
