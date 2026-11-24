-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c
-- name    : P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:03.052373+00:00
-- url     : https://prove2.me/theorems/64d99778-4d08-4fcc-9bbc-ebd707595ad0
-- title:
--   P2 M Ground Theory Heights  Heights coord Vec ne zero 81a696e5203c: P2 M Ground Theory Heights  Heights coord Vec ne zero 81a696e5203c
-- statement:
--   The P2 M Ground Theory Heights  Heights coord Vec ne zero 81a696e5203c construction uses the P2 M Ground Theory Heights  Heights coord Vec ne zero 81a696e5203c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L184-L189

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) (k : ι) :
    coordVec x k ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coordVec_ne_zero» := P2M_GroundTheory_Heights__Heights_coordVec_ne_zero_81a696e5203c
