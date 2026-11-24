-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:26.792812+00:00
-- url     : https://prove2.me/theorems/b9a60f11-d554-423a-ba33-2dcd8df4d967
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi map C 3e351123070f: P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi map C 3e351123070f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi map C 3e351123070f construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin phi map C 3e351123070f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L101-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/PsiOfIsHomogeneous.lean#L101-L125

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    phi x η S (MvPolynomial.map (C : S →+* Sy S r) f) = single ((e : ℤ), (0 : ℤ)) (aeval x f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«phi_map_C» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f
