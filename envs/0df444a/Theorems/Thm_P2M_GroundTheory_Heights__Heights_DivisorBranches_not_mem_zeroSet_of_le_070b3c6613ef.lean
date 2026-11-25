-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorBranches_not_mem_zeroSet_of_le_070b3c6613ef
-- name    : P2M_GroundTheory_Heights__Heights_DivisorBranches_not_mem_zeroSet_of_le_070b3c6613ef
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:00.604824+00:00
-- url     : https://prove2.me/theorems/7bfb8ec6-d6d6-53c1-af23-980084f769f5
-- title:
--   P2 M Ground Theory Heights  Heights Divisor Branches not mem zero Set of le 070b3c6613ef: P2 M Ground Theory Heights  Heights Divisor Branches not mem zero Set of le 070b3c6613ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor Branches not mem zero Set of le 070b3c6613ef construction uses the P2 M Ground Theory Heights  Heights Divisor Branches not mem zero Set of le 070b3c6613ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L35-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorRegularGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorBranches
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
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorBranches

theorem P2M_GroundTheory_Heights__Heights_DivisorBranches_not_mem_zeroSet_of_le_070b3c6613ef {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorBranches».«not_mem_zeroSet_of_le» := P2M_GroundTheory_Heights__Heights_DivisorBranches_not_mem_zeroSet_of_le_070b3c6613ef
