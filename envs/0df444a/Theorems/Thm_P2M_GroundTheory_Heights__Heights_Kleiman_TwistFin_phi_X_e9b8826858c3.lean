-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:07.023422+00:00
-- url     : https://prove2.me/theorems/e9ef904a-ee1f-49a6-8b99-121cc6ab3492
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi X e9b8826858c3: P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi X e9b8826858c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi X e9b8826858c3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi X e9b8826858c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L50-L51

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3 (i : Fin (N + 1)) : phi x η S (X i) = single ((1 : ℤ), (0 : ℤ)) (x i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«phi_X» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3
