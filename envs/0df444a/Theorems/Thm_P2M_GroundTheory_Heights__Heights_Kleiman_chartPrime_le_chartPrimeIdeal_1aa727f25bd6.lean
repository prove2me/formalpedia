-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:54.134545+00:00
-- url     : https://prove2.me/theorems/5245f027-1ffd-44cb-b89b-c29c29ad6989
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman chart Prime le chart Prime Ideal 1aa727f25bd6: P2 M Ground Theory Heights  Heights Kleiman chart Prime le chart Prime Ideal 1aa727f25bd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman chart Prime le chart Prime Ideal 1aa727f25bd6 construction uses the P2 M Ground Theory Heights  Heights Kleiman chart Prime le chart Prime Ideal 1aa727f25bd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationPoint.lean#L108-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
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
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6 (hj : x j ≠ 0) (pp : Ideal (Poly S N)) :
    chartPrime pp hj ≤ chartPrimeIdeal x hj pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«chartPrime_le_chartPrimeIdeal» := P2M_GroundTheory_Heights__Heights_Kleiman_chartPrime_le_chartPrimeIdeal_1aa727f25bd6
