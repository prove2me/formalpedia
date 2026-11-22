-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
-- name    : Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:31.965314+00:00
-- url     : https://prove2.me/theorems/175b6de8-dbc2-4443-8c99-6834e6642fa4
-- title:
--   Ainf Inv: lift Frac Witt algebra Map
-- statement:
--   The Ainf Inv construction uses the lift Frac Witt algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L147-L149

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    AinfInv.liftFracWitt p g (algebraMap _ _ a) = algebraMap _ _ (Ainf.liftWitt p g a) := by sorry
