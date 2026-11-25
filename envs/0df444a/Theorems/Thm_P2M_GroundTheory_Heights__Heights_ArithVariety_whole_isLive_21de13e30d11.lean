-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:48.492506+00:00
-- url     : https://prove2.me/theorems/565d1d48-1919-4233-bd58-b35022380d84
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety whole is Live 21de13e30d11: P2 M Ground Theory Heights  Heights Arith Variety whole is Live 21de13e30d11
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety whole is Live 21de13e30d11 construction uses the P2 M Ground Theory Heights  Heights Arith Variety whole is Live 21de13e30d11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Examples.lean#L29-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11 (c : (k : ι) → Fin (n k + 1)) : (whole n).IsLive c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«whole_isLive» := P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isLive_21de13e30d11
