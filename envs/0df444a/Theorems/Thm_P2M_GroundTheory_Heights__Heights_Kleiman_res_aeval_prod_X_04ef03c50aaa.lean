-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:24:19.795729+00:00
-- url     : https://prove2.me/theorems/848c63eb-ebd3-4a64-863c-4581b9a7c7b3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman res aeval prod X 04ef03c50aaa: P2 M Ground Theory Heights  Heights Kleiman res aeval prod X 04ef03c50aaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman res aeval prod X 04ef03c50aaa construction uses the P2 M Ground Theory Heights  Heights Kleiman res aeval prod X 04ef03c50aaa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/RestrictionPowers.lean#L121-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa (s : Finset (Fin (N + 1))) :
    aeval x (∏ i ∈ s, (X i : Poly S N)) = ∏ i ∈ s, x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«res_aeval_prod_X» := P2M_GroundTheory_Heights__Heights_Kleiman_res_aeval_prod_X_04ef03c50aaa
