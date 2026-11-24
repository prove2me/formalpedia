-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:44.55411+00:00
-- url     : https://prove2.me/theorems/1a8228f9-4ce9-4585-b4cb-0bb8faad1a45
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff of fin zero 39ff712c69c1: P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff of fin zero 39ff712c69c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff of fin zero 39ff712c69c1 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel mixed Diff of fin zero 39ff712c69c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PDegLTGrowth.lean#L15-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegLTGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegLTGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type} [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1 (bs : Fin 0 → K → ℤ) (f : (K → ℤ) → ℤ) : mixedDiff bs f = f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«mixedDiff_of_fin_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_mixedDiff_of_fin_zero_39ff712c69c1
