-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:24.463398+00:00
-- url     : https://prove2.me/theorems/ee07a6fe-12d4-468d-8b87-90f28e29a21b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi X 102517a1af24: P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi X 102517a1af24
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi X 102517a1af24 construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin psi X 102517a1af24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L53-L54

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24 (j : Fin (r + 1)) : psi η S (X j) = single ((0 : ℤ), (1 : ℤ)) (η j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«psi_X» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
