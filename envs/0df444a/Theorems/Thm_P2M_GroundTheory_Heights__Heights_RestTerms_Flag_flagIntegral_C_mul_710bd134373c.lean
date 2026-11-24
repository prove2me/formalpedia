-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:41.935447+00:00
-- url     : https://prove2.me/theorems/1c8ca8e2-8a9c-4499-aa39-ada2017f0ecf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral C mul 710bd134373c: P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral C mul 710bd134373c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral C mul 710bd134373c construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag flag Integral C mul 710bd134373c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L215-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean#L215-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
variable (f r a : ℕ) (c : SmallBlock)

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c (f N : ℕ) (x : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C x * Φ) = x * flagIntegral f N Φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«flagIntegral_C_mul» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c
