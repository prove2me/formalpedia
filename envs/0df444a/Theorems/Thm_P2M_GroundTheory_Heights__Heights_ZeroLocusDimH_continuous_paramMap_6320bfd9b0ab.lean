-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:46.756504+00:00
-- url     : https://prove2.me/theorems/897e8d7e-1506-4af7-8a75-c48e2c7d234e
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H continuous param Map 6320bfd9b0ab: P2 M Ground Theory Heights  Heights Zero Locus Dim H continuous param Map 6320bfd9b0ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H continuous param Map 6320bfd9b0ab construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H continuous param Map 6320bfd9b0ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L112-L114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab {n r : ℕ} (π : Fin r → MvPolynomial (Fin n) ℂ) :
    Continuous (paramMap π) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«continuous_paramMap» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_continuous_paramMap_6320bfd9b0ab
