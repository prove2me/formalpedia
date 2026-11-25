-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_locEmb_eq_6cc96fc5108f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_exists_locEmb_eq_6cc96fc5108f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:12.771124+00:00
-- url     : https://prove2.me/theorems/df5d37a2-c5e7-4e42-81dc-18f1bf3074d2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman exists loc Emb eq 6cc96fc5108f: P2 M Ground Theory Heights  Heights Kleiman exists loc Emb eq 6cc96fc5108f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman exists loc Emb eq 6cc96fc5108f construction uses the P2 M Ground Theory Heights  Heights Kleiman exists loc Emb eq 6cc96fc5108f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L209-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L209-L235

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_exists_locEmb_eq_6cc96fc5108f (I : StdCell N) (hI : I.1 ⊆ support x) {b c : ℤ} {y : Ω}
    (hy : y ∈ twLocPart η M₀ b c I.1) :
    ∃ w ∈ degLoc (twGraded η M₀) c I, UT.toL (locEmb η M₀ I.1 hI w) = single (b, c) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«exists_locEmb_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_exists_locEmb_eq_6cc96fc5108f
