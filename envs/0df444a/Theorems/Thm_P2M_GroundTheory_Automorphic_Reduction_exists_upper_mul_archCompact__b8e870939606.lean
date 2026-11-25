-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606
-- name    : P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:37:50.99261+00:00
-- url     : https://prove2.me/theorems/3eed7e70-6dff-4c10-8078-de63f03cb676
-- title:
--   P2 M Ground Theory Automorphic Reduction exists upper mul arch Compact  b8e870939606: P2 M Ground Theory Automorphic Reduction exists upper mul arch Compact  b8e870939606
-- statement:
--   The P2 M Ground Theory Automorphic Reduction exists upper mul arch Compact  b8e870939606 construction uses the P2 M Ground Theory Automorphic Reduction exists upper mul arch Compact  b8e870939606 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L171-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L171-L176

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]
omit [NumberField K]

theorem P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606 (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ p : GL (Fin n) w.Completion × GL (Fin n) w.Completion,
      (p.1 : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧ p.2 ∈ archCompact w ∧
        h = p.1 * p.2 := by sorry

alias «GroundTheory».«Automorphic».«Reduction».«exists_upper_mul_archCompact'» := P2M_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact__b8e870939606
