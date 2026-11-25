-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistSub_le_twLocPart_4309e71487a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twistSub_le_twLocPart_4309e71487a8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:26.575634+00:00
-- url     : https://prove2.me/theorems/c38952c0-db29-4a30-b814-3efd9de47a0e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist Sub le tw Loc Part 4309e71487a8: P2 M Ground Theory Heights  Heights Kleiman twist Sub le tw Loc Part 4309e71487a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist Sub le tw Loc Part 4309e71487a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist Sub le tw Loc Part 4309e71487a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L116-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L116-L137

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
variable {G B : SubSystem S x Ω}
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twistSub_le_twLocPart_4309e71487a8 (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    y ∈ twLocPart η M₀ n c K.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twistSub_le_twLocPart» := P2M_GroundTheory_Heights__Heights_Kleiman_twistSub_le_twLocPart_4309e71487a8
