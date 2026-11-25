-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:11:48.198916+00:00
-- url     : https://prove2.me/theorems/38626f18-de90-5ff5-8ada-a5e5cb84a39c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman twist tilde Sys mono af7572066c54: P2 M Ground Theory Heights  Heights Kleiman twist tilde Sys mono af7572066c54
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman twist tilde Sys mono af7572066c54 construction uses the P2 M Ground Theory Heights  Heights Kleiman twist tilde Sys mono af7572066c54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PClaimVanish.lean#L53-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54 {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«twist_tildeSys_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_twist_tildeSys_mono_af7572066c54
