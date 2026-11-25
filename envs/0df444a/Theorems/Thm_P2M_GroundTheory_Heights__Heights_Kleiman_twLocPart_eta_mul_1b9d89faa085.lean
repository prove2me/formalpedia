-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_eta_mul_1b9d89faa085
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_eta_mul_1b9d89faa085
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:03:45.238452+00:00
-- url     : https://prove2.me/theorems/216eca9c-5613-47cc-94f7-289aa34e6db8
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tw Loc Part eta mul 1b9d89faa085: P2 M Ground Theory Heights  Heights Kleiman tw Loc Part eta mul 1b9d89faa085
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tw Loc Part eta mul 1b9d89faa085 construction uses the P2 M Ground Theory Heights  Heights Kleiman tw Loc Part eta mul 1b9d89faa085 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L23-L31

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
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
open MvPolynomial Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_eta_mul_1b9d89faa085 (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} {I : Finset (Fin (N + 1))}
    (j : Fin (r + 1)) {y : Ω} (hy : y ∈ twLocPart η M₀ b c I) : η j * y ∈ twLocPart η M₀ (b + 1) c I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twLocPart_eta_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_eta_mul_1b9d89faa085
