-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:19.533277+00:00
-- url     : https://prove2.me/theorems/18715337-dd1f-4b9a-8aeb-58df7713df8b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi mem tgr 0b163f9c37ae: P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi mem tgr 0b163f9c37ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi mem tgr 0b163f9c37ae construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi mem tgr 0b163f9c37ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L79-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae {p : Poly (Sy S r) N} {d : ℕ} (hp : p.IsHomogeneous d) :
    phi x η S p ∈ tgr (d : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«phi_mem_tgr» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_mem_tgr_0b163f9c37ae
