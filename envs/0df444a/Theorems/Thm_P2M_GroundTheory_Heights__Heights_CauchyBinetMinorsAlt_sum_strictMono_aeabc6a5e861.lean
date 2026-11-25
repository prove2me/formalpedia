-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:36.656944+00:00
-- url     : https://prove2.me/theorems/5abe9426-bcd8-486d-ad57-c0e679cf71e9
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum strict Mono aeabc6a5e861: P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum strict Mono aeabc6a5e861
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum strict Mono aeabc6a5e861 construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Minors Alt sum strict Mono aeabc6a5e861 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L39-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCauchyBinetMinors.lean#L39-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCauchyBinetMinors
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
open Matrix Finset
open GroundTheory.Heights₂.Heights.CauchyBinetMinorsAlt

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861 {n k : ℕ} {β : Type*} [AddCommMonoid β]
    [DecidablePred (fun b : Fin k → Fin n => StrictMono b)] (g : (Fin k → Fin n) → β) :
    ∑ b ∈ univ.filter (fun b : Fin k → Fin n => StrictMono b), g b =
      ∑ S : {S : Finset (Fin n) // S.card = k}, g (S.1.orderEmbOfFin S.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetMinorsAlt».«sum_strictMono» := P2M_GroundTheory_Heights__Heights_CauchyBinetMinorsAlt_sum_strictMono_aeabc6a5e861
