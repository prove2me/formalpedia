-- Prove2me | Theorems.Thm_Reformulated_AutPerF_PFlat_twist_twist
-- name    : Reformulated.AutPerF.PFlat.twist_twist
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:52.39335+00:00
-- url     : https://prove2.me/theorems/97cff4aa-ec4a-4592-b481-3de36e6468de
-- title:
--   PFlat: twist twist
-- statement:
--   The PFlat construction uses the twist twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L349-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/MapEqPadicPowCyclotomicCharacter.lean#L349-L350

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
open Tilt tateModule
open Reformulated.AutPerF.PFlat

theorem Reformulated.AutPerF.PFlat.twist_twist (η η' : tateModule p R) (ϖ : PFlat p R) :
    (ϖ.twist η').twist η = ϖ.twist (η * η') := by sorry
