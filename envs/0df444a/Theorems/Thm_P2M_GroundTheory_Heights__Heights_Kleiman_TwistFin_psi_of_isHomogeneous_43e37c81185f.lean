-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:43.700986+00:00
-- url     : https://prove2.me/theorems/01b06606-5328-479f-b957-84a38fc6837c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi of is Homogeneous 43e37c81185f: P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi of is Homogeneous 43e37c81185f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi of is Homogeneous 43e37c81185f construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi of is Homogeneous 43e37c81185f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L127-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L127-L146

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f {h : Sy S r} {b : ℕ} (hh : h.IsHomogeneous b) :
    psi η S h = single ((0 : ℤ), (b : ℤ)) (aeval η h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«psi_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f
