-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:42.239814+00:00
-- url     : https://prove2.me/theorems/1f55936b-12ae-5704-9a1e-eed852a267ee
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone E mk f17973bed795: P2 M Ground Theory Heights  Heights Kleiman loc Cone E mk f17973bed795
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone E mk f17973bed795 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone E mk f17973bed795 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeVanishLoc.lean#L26-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795 (I : Finset (Fin (N + 1))) (hI : I ⊆ support x) (m : M.coneSubE)
    (s : monos (S := S) I) :
    (s : Poly S N) • locConeE M I hI (LocalizedModule.mk m s) = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locConeE_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795
