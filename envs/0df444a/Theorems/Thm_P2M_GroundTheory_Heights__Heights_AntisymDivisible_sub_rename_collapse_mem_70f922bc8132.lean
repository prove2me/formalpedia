-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132
-- name    : P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:15.518904+00:00
-- url     : https://prove2.me/theorems/0aef9dc6-aea5-4315-a298-580e9f14ad11
-- title:
--   P2 M Ground Theory Heights  Heights Antisym Divisible sub rename collapse mem 70f922bc8132: P2 M Ground Theory Heights  Heights Antisym Divisible sub rename collapse mem 70f922bc8132
-- statement:
--   The P2 M Ground Theory Heights  Heights Antisym Divisible sub rename collapse mem 70f922bc8132 construction uses the P2 M Ground Theory Heights  Heights Antisym Divisible sub rename collapse mem 70f922bc8132 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PAntisymDivisible.lean#L26-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132 (u v : σ) (P : MvPolynomial σ ℝ) :
    P - rename (collapse u v) P ∈ Ideal.span {(X u - X v : MvPolynomial σ ℝ)} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AntisymDivisible».«sub_rename_collapse_mem» := P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132
