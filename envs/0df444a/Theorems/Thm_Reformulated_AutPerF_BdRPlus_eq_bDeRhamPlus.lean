-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_eq_bDeRhamPlus
-- name    : Reformulated.AutPerF.BdRPlus.eq_bDeRhamPlus
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:38.580181+00:00
-- url     : https://prove2.me/theorems/e18d48c5-eb1e-4e13-9e69-1a0358635b5b
-- title:
--   Bd RPlus: eq b De Rham Plus
-- statement:
--   The Bd RPlus construction uses the eq b De Rham Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L109-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L109-L109

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus

theorem Reformulated.AutPerF.BdRPlus.eq_bDeRhamPlus : BdRPlus p R = BDeRhamPlus R p := by sorry
