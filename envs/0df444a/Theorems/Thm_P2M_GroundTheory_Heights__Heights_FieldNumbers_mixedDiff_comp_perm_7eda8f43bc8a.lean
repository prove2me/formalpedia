-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:28.443049+00:00
-- url     : https://prove2.me/theorems/cd7faa93-77c3-4050-bc91-aadada81e72e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mixed Diff comp perm 7eda8f43bc8a: P2 M Ground Theory Heights  Heights Field Numbers mixed Diff comp perm 7eda8f43bc8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mixed Diff comp perm 7eda8f43bc8a construction uses the P2 M Ground Theory Heights  Heights Field Numbers mixed Diff comp perm 7eda8f43bc8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumSymm.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumSymm.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a {n : ℕ} (bs : Fin n → K → ℤ) (σ : Equiv.Perm (Fin n))
    (h : (K → ℤ) → ℤ) : mixedDiff (bs ∘ σ) h = mixedDiff bs h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mixedDiff_comp_perm» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a
