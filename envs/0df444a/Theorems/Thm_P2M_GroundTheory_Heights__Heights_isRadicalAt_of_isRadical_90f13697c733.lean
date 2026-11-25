-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733
-- name    : P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:15.111357+00:00
-- url     : https://prove2.me/theorems/e5ff017c-88c3-46a2-987e-4eb3bba355e8
-- title:
--   P2 M Ground Theory Heights  Heights is Radical At of is Radical 90f13697c733: P2 M Ground Theory Heights  Heights is Radical At of is Radical 90f13697c733
-- statement:
--   The P2 M Ground Theory Heights  Heights is Radical At of is Radical 90f13697c733 construction uses the P2 M Ground Theory Heights  Heights is Radical At of is Radical 90f13697c733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L41-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
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
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733 {I : Ideal (MvPolynomial (Fin n) ℂ)} (hI : I.IsRadical)
    (q : Fin n → ℂ) : IsRadicalAt I q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isRadicalAt_of_isRadical» := P2M_GroundTheory_Heights__Heights_isRadicalAt_of_isRadical_90f13697c733
