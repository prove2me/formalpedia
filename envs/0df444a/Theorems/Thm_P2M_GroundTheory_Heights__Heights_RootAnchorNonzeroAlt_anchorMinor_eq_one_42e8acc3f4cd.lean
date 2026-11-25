-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_anchorMinor_eq_one_42e8acc3f4cd
-- name    : P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_anchorMinor_eq_one_42e8acc3f4cd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:45.040471+00:00
-- url     : https://prove2.me/theorems/2abfb2e5-8564-417e-a487-f216708e0a9a
-- title:
--   P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt anchor Minor eq one 42e8acc3f4cd: P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt anchor Minor eq one 42e8acc3f4cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt anchor Minor eq one 42e8acc3f4cd construction uses the P2 M Ground Theory Heights  Heights Root Anchor Nonzero Alt anchor Minor eq one 42e8acc3f4cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean#L13-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootAnchorNonzeroAlt

theorem P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_anchorMinor_eq_one_42e8acc3f4cd {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootAnchorNonzeroAlt».«anchorMinor_eq_one» := P2M_GroundTheory_Heights__Heights_RootAnchorNonzeroAlt_anchorMinor_eq_one_42e8acc3f4cd
