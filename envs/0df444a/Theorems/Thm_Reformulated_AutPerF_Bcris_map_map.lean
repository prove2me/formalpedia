-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bcris_map_map
-- name    : Reformulated.AutPerF.Bcris.map_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:52:18.457504+00:00
-- url     : https://prove2.me/theorems/79f66a49-7125-4963-ad46-2ed5a625c00f
-- title:
--   Bcris: map map
-- statement:
--   The Bcris construction uses the map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L398-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/ExistsFactorialMulEqPow.lean#L398-L402

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_map

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

theorem Reformulated.AutPerF.Bcris.map_map (f : R →+* S) (hf : Function.Injective f) (g : S →+* U)
    (hg : Function.Injective g) (hgf : Function.Injective (g.comp f)) (x : Bcris p R) :
    map p g hg (map p f hf x) = map p (g.comp f) hgf x := by sorry
