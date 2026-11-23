-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Tilt_seq_map
-- name    : Reformulated.AutPerF.Tilt.seq_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:06.066988+00:00
-- url     : https://prove2.me/theorems/c889522b-7b82-46cc-87a0-10f344e2cf49
-- title:
--   Tilt: seq map
-- statement:
--   The Tilt construction uses the seq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L69-L74

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_MapEqPadicPowCyclotomicCharacter
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
open Reformulated Reformulated.AutPerF
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
open Reformulated.AutPerF.Tilt

theorem Reformulated.AutPerF.Tilt.seq_map (f : R →+* S) (y : Tilt p R) (n : ℕ) : seq n (map p f y) = f (seq n y) := by sorry
