-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:37.774463+00:00
-- url     : https://prove2.me/theorems/68ccaf04-70d7-5200-9ef5-ae47d1091969
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman loc Cone mk eq 99b34d9786d2: P2 M Ground Theory Heights  Heights Kleiman loc Cone mk eq 99b34d9786d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman loc Cone mk eq 99b34d9786d2 construction uses the P2 M Ground Theory Heights  Heights Kleiman loc Cone mk eq 99b34d9786d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeTailLoc.lean#L57-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2 {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSub}
    {s : monos (S := S) I} {w : ConeLaurent S x} (h : coneLaurent S x s * w = m) :
    locCone M I hI (LocalizedModule.mk m s) = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«locCone_mk_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
