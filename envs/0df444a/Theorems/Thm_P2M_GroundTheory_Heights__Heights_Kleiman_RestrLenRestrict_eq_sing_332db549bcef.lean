-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_eq_sing_332db549bcef
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_eq_sing_332db549bcef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:21.607155+00:00
-- url     : https://prove2.me/theorems/92c4863f-53f1-5695-b5eb-26d57a6cf844
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict eq sing 332db549bcef: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict eq sing 332db549bcef
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict eq sing 332db549bcef construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict eq sing 332db549bcef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L97-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_eq_sing_332db549bcef (I : Cech.Idx (support x) 0) : ∃ (a : Fin (N + 1)) (ha : a ∈ support x), I = sing ha := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«eq_sing» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_eq_sing_332db549bcef
