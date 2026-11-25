-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_redGood_fb99db1a608a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_redGood_fb99db1a608a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:58.499002+00:00
-- url     : https://prove2.me/theorems/76d07686-1aea-531a-b4f8-5b19ddcc61f0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists red Good fb99db1a608a: P2 M Ground Theory Heights  Heights Kleiman exists red Good fb99db1a608a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists red Good fb99db1a608a construction uses the P2 M Ground Theory Heights  Heights Kleiman exists red Good fb99db1a608a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L32-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionBundle.lean#L32-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionSystems
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
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
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
  (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
  {Nb : LineBundle k x} {r : ℕ} {h : Fin (r + 1) → Ω}
include hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_redGood_fb99db1a608a (hV : IsVeryAmpleBy Nb.toSubSystem h) (I₀ : Chart y) :
    ∃ l₀ : Fin (r + 1), h l₀ ≠ 0 ∧ (∀ l, h l / h l₀ ∈ locAt k x y) ∧
      RedGood hxy Nb.toSubSystem (h l₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_redGood» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_redGood_fb99db1a608a
