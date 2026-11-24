-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_le_dimFl_f78b9b4583b1
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_le_dimFl_f78b9b4583b1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:57.793801+00:00
-- url     : https://prove2.me/theorems/bace6181-bbbc-4bdf-a56a-8523da66c0c3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq le dim Fl f78b9b4583b1: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq le dim Fl f78b9b4583b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq le dim Fl f78b9b4583b1 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq le dim Fl f78b9b4583b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_le_dimFl_f78b9b4583b1 (f j k : ℕ) (hf : 1 ≤ f) : j + k ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k + 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«le_dimFl» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_le_dimFl_f78b9b4583b1
