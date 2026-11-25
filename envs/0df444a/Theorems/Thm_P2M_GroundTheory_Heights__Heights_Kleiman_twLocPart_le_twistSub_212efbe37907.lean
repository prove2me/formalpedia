-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_le_twistSub_212efbe37907
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_le_twistSub_212efbe37907
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:50.48449+00:00
-- url     : https://prove2.me/theorems/c209f66b-a5b2-4ab7-bf4d-f3d90917fb9d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tw Loc Part le twist Sub 212efbe37907: P2 M Ground Theory Heights  Heights Kleiman tw Loc Part le twist Sub 212efbe37907
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tw Loc Part le twist Sub 212efbe37907 construction uses the P2 M Ground Theory Heights  Heights Kleiman tw Loc Part le twist Sub 212efbe37907 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L139-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean#L139-L177

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_le_twistSub_212efbe37907 (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ twLocPart η M₀ n c K.1) :
    y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twLocPart_le_twistSub» := P2M_GroundTheory_Heights__Heights_Kleiman_twLocPart_le_twistSub_212efbe37907
