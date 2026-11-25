-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_map_C_mem_monos_9cd0e7dd150b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_map_C_mem_monos_9cd0e7dd150b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:01:18.744867+00:00
-- url     : https://prove2.me/theorems/ab42f0b8-b472-562a-a404-e95fa18923ef
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Twist Fin map C mem monos 9cd0e7dd150b: P2 M Ground Theory Heights  Heights Kleiman Twist Fin map C mem monos 9cd0e7dd150b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Twist Fin map C mem monos 9cd0e7dd150b construction uses the P2 M Ground Theory Heights  Heights Kleiman Twist Fin map C mem monos 9cd0e7dd150b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
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
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_map_C_mem_monos_9cd0e7dd150b {I : Finset (Fin (N + 1))} {t : Poly S N} (ht : t ∈ monos (S := S) I) :
    MvPolynomial.map (C : S →+* Sy S r) t ∈ monos (S := Sy S r) I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«TwistFin».«map_C_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_map_C_mem_monos_9cd0e7dd150b
