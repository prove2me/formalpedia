-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_zeroSet_sup_span_be5eee703857
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_zeroSet_sup_span_be5eee703857
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:01.950266+00:00
-- url     : https://prove2.me/theorems/e19d9cf3-e141-513e-bf1b-51faeb3fa85b
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets zero Set sup span be5eee703857: P2 M Ground Theory Heights  Heights Complex Sets zero Set sup span be5eee703857
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets zero Set sup span be5eee703857 construction uses the P2 M Ground Theory Heights  Heights Complex Sets zero Set sup span be5eee703857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBadSetSmaller.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PBadSetSmaller.lean#L23-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBadSetSmaller
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_zeroSet_sup_span_be5eee703857 {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    zeroSet (J ⊔ Ideal.span {f}) = zeroSet J ∩ {x | eval x f = 0} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«zeroSet_sup_span» := P2M_GroundTheory_Heights__Heights_ComplexSets_zeroSet_sup_span_be5eee703857
