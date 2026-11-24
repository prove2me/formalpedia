-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
-- name    : P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:12.22538+00:00
-- url     : https://prove2.me/theorems/11b69ac9-8f11-47a5-aa08-33e845a79f60
-- title:
--   P2 M Ground Theory Heights  Heights fund Cycle apply of is Radical cfa81f886234: P2 M Ground Theory Heights  Heights fund Cycle apply of is Radical cfa81f886234
-- statement:
--   The P2 M Ground Theory Heights  Heights fund Cycle apply of is Radical cfa81f886234 construction uses the P2 M Ground Theory Heights  Heights fund Cycle apply of is Radical cfa81f886234 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LocalMultRadical.lean#L27-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
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

theorem P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234 {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) R)} (hJ : J.IsRadical) {W : Ideal (MvPolynomial (Fin n) R)}
    (hW : W ∈ (fundCycle J).support) : fundCycle J W = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fundCycle_apply_of_isRadical» := P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
