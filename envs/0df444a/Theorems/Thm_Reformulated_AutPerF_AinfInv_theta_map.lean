-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
-- name    : Reformulated.AutPerF.AinfInv.theta_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:19.86781+00:00
-- url     : https://prove2.me/theorems/e6228bff-bfa5-4920-bcc6-09b55ae43527
-- title:
--   Ainf Inv: theta map
-- statement:
--   The Ainf Inv construction uses the theta map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L325-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L325-L329

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
variable {p}

theorem Reformulated.AutPerF.AinfInv.theta_map [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
    (f : R →+* S) (x : AinfInv p R) :
    AinfInv.theta p S (AinfInv.map p f x) = awayMap p f (AinfInv.theta p R x) := by sorry
