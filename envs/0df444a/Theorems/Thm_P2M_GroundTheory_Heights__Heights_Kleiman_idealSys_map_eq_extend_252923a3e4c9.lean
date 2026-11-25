-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealSys_map_eq_extend_252923a3e4c9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_idealSys_map_eq_extend_252923a3e4c9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:13:37.254379+00:00
-- url     : https://prove2.me/theorems/40b5010a-3f9e-510b-8832-9660fc409c76
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman ideal Sys map eq extend 252923a3e4c9: P2 M Ground Theory Heights  Heights Kleiman ideal Sys map eq extend 252923a3e4c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman ideal Sys map eq extend 252923a3e4c9 construction uses the P2 M Ground Theory Heights  Heights Kleiman ideal Sys map eq extend 252923a3e4c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L112-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PGenericRestrLen.lean#L112-L145

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenericRestrLen
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
variable {S : Type u} [CommRing S] {F : Type u} [Field F] [Algebra S F] {N : ℕ}
variable [IsFractionRing S F] {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra F Ω] [IsScalarTower S F Ω]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_idealSys_map_eq_extend_252923a3e4c9 (x : Fin (N + 1) → Ω) (qq : Ideal (Poly S N))
    (hq : ∀ p ∈ qq, ∀ d : ℕ, homogeneousComponent d p ∈ qq) :
    idealSys x (qq.map (MvPolynomial.map (algebraMap S F))) = (idealSys x qq).extend F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«idealSys_map_eq_extend» := P2M_GroundTheory_Heights__Heights_Kleiman_idealSys_map_eq_extend_252923a3e4c9
