-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twLocMod_subsingleton_be78395e6bcf
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twLocMod_subsingleton_be78395e6bcf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:05:09.85387+00:00
-- url     : https://prove2.me/theorems/695fddcc-f67e-55b0-93b3-92c91f81e9fa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman tw Loc Mod subsingleton be78395e6bcf: P2 M Ground Theory Heights  Heights Kleiman tw Loc Mod subsingleton be78395e6bcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman tw Loc Mod subsingleton be78395e6bcf construction uses the P2 M Ground Theory Heights  Heights Kleiman tw Loc Mod subsingleton be78395e6bcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L137-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitLoc.lean#L137-L154

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twLocMod_subsingleton_be78395e6bcf {J : Finset (Fin (N + 1))} (hJ : ¬ J ⊆ support x) :
    Subsingleton (LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twLocMod_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_twLocMod_subsingleton_be78395e6bcf
