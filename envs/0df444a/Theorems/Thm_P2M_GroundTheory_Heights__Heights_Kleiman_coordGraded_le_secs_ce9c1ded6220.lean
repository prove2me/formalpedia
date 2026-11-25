-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_le_secs_ce9c1ded6220
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_le_secs_ce9c1ded6220
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:23.108621+00:00
-- url     : https://prove2.me/theorems/5fa20bc4-8e08-56e0-b457-b22bac144329
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coord Graded le secs ce9c1ded6220: P2 M Ground Theory Heights  Heights Kleiman coord Graded le secs ce9c1ded6220
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coord Graded le secs ce9c1ded6220 construction uses the P2 M Ground Theory Heights  Heights Kleiman coord Graded le secs ce9c1ded6220 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_le_secs_ce9c1ded6220 (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coordGraded_le_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_le_secs_ce9c1ded6220
