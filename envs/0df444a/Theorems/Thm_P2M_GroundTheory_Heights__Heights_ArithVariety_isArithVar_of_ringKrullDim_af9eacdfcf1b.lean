-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:37.175468+00:00
-- url     : https://prove2.me/theorems/6064a3fb-5ce8-4a00-a91f-1cd566e5df59
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety is Arith Var of ring Krull Dim af9eacdfcf1b: P2 M Ground Theory Heights  Heights Arith Variety is Arith Var of ring Krull Dim af9eacdfcf1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety is Arith Var of ring Krull Dim af9eacdfcf1b construction uses the P2 M Ground Theory Heights  Heights Arith Variety is Arith Var of ring Krull Dim af9eacdfcf1b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsArithVarOfRingKrullDim.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsArithVarOfRingKrullDim.lean#L9-L13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsArithVarOfRingKrullDim
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ι → ℕ} (P : ArithVariety n) {D : ℕ}
    (hdim : ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞)) :
    Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«isArithVar_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b
