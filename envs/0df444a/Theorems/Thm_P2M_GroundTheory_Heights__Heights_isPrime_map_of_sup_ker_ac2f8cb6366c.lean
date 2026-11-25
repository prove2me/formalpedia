-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_of_sup_ker_ac2f8cb6366c
-- name    : P2M_GroundTheory_Heights__Heights_isPrime_map_of_sup_ker_ac2f8cb6366c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:04.721724+00:00
-- url     : https://prove2.me/theorems/ef78cb7f-ee3f-4437-828f-d889ad958863
-- title:
--   P2 M Ground Theory Heights  Heights is Prime map of sup ker ac2f8cb6366c: P2 M Ground Theory Heights  Heights is Prime map of sup ker ac2f8cb6366c
-- statement:
--   The P2 M Ground Theory Heights  Heights is Prime map of sup ker ac2f8cb6366c construction uses the P2 M Ground Theory Heights  Heights is Prime map of sup ker ac2f8cb6366c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartIncOrd.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartIncOrd.lean#L23-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isPrime_map_of_sup_ker_ac2f8cb6366c {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (K : Ideal R) (h : (K ⊔ RingHom.ker f).IsPrime) : (K.map f).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isPrime_map_of_sup_ker» := P2M_GroundTheory_Heights__Heights_isPrime_map_of_sup_ker_ac2f8cb6366c
