-- Prove2me | Theorems.Thm_Reformulated_AutPerF_padic_hom_ext
-- name    : Reformulated.AutPerF.padic_hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:43.729339+00:00
-- url     : https://prove2.me/theorems/1815e581-e909-4639-a1b6-d42b7d814957
-- title:
--   Aut Per F: padic hom ext
-- statement:
--   The Aut Per F construction uses the padic hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L265-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/SpanNatCastLeComap.lean#L265-L267

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

theorem Reformulated.AutPerF.padic_hom_ext {B : Type*} [CommRing B] {f g : ℚ_[p] →+* B}
    (h : ∀ a : ℤ_[p], f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by sorry
