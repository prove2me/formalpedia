-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_p_dvd_frob_sub_pow
-- name    : Reformulated.AutPerF.Ainf.p_dvd_frob_sub_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:15.650794+00:00
-- url     : https://prove2.me/theorems/7ca18724-6821-407e-b7d6-904f6f046d37
-- title:
--   Ainf: p dvd frob sub pow
-- statement:
--   The Ainf construction uses the p dvd frob sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L194-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L194-L197

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
variable {R S U}
open Reformulated.AutPerF.Ainf
variable {p}

theorem Reformulated.AutPerF.Ainf.p_dvd_frob_sub_pow (x : Ainf p R) : (p : Ainf p R) ∣ frob p R x - x ^ p := by sorry
