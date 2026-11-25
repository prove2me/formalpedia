-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:04.763819+00:00
-- url     : https://prove2.me/theorems/fbd00e8c-7b57-5f03-9743-e566e2a57798
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman section Exists of gap fdd95ec62f45: P2 M Ground Theory Heights  Heights Kleiman section Exists of gap fdd95ec62f45
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman section Exists of gap fdd95ec62f45 construction uses the P2 M Ground Theory Heights  Heights Kleiman section Exists of gap fdd95ec62f45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L39-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionExists.lean#L39-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists
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
open Filter
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45 (hcount : SectionCount.Statement.{u, w})
    (hlead : LeadingCoeffPos.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {d : ℕ} {M : LineBundle k x} {t s' : ℚ}
    (hZ : IsSubvar x (primeOf (S := k) x) (d + 1)) (hM : Nef M.toSubSystem) (hs' : 0 < s')
    {Q : ℕ} {mQ : ℤ} (hQ : 0 < Q) (hmQ : (mQ : ℚ) = Q * t)
    (hva : IsVeryAmple (twistMul M.toSubSystem Q mQ))
    (hgap : 1 < (Q : ℚ) * (t / (d + 1) - s')) :
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«sectionExists_of_gap» := P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45
