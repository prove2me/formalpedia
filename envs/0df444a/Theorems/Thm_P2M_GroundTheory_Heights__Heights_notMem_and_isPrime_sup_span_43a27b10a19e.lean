-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e
-- name    : P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:46.208716+00:00
-- url     : https://prove2.me/theorems/93006480-c8d6-49ff-8e8b-4f51bfe22a60
-- title:
--   P2 M Ground Theory Heights  Heights not Mem and is Prime sup span 43a27b10a19e: P2 M Ground Theory Heights  Heights not Mem and is Prime sup span 43a27b10a19e
-- statement:
--   The P2 M Ground Theory Heights  Heights not Mem and is Prime sup span 43a27b10a19e construction uses the P2 M Ground Theory Heights  Heights not Mem and is Prime sup span 43a27b10a19e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L71-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L71-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«notMem_and_isPrime_sup_span» := P2M_GroundTheory_Heights__Heights_notMem_and_isPrime_sup_span_43a27b10a19e
