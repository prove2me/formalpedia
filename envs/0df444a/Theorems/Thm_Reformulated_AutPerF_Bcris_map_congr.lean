-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bcris_map_congr
-- name    : Reformulated.AutPerF.Bcris.map_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:38.228656+00:00
-- url     : https://prove2.me/theorems/2fa6e96c-0c29-5e86-8cfe-b6c072aad8c6
-- title:
--   Bcris: map congr
-- statement:
--   The Bcris construction uses the map congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L404-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L404-L405

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
variable {p}
open Reformulated.AutPerF.Bcris

theorem Reformulated.AutPerF.Bcris.map_congr {f g : R →+* S} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f = g) : map p f hf = map p g hg := by sorry
