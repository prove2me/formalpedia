-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:20.474221+00:00
-- url     : https://prove2.me/theorems/409b588b-6108-4efb-b2c0-8208fb9cee86
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq of sum eq nsmul of norm le 831fa282c107: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq of sum eq nsmul of norm le 831fa282c107 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eq of sum eq nsmul of norm le 831fa282c107 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalMaximumPrinciple.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalMaximumPrinciple.lean#L10-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalMaximumPrinciple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter RealInnerProductSpace

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (c : E) (hle : ∀ j, ‖a j‖ ≤ ‖c‖) (hsum : ∑ j, a j = m • c) (j : Fin m) :
    a j = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eq_of_sum_eq_nsmul_of_norm_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eq_of_sum_eq_nsmul_of_norm_le_831fa282c107
