-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
-- name    : Reformulated.AutPerF.Ainf.ofWitt_teichmuller
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:18.749782+00:00
-- url     : https://prove2.me/theorems/6efa6761-5d2b-4ae7-b802-abcfc2c008b5
-- title:
--   Ainf: of Witt teichmuller
-- statement:
--   The Ainf construction uses the of Witt teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L42-L44

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
variable {k : Type w} [CommRing k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.Ainf.ofWitt_teichmuller (f : k →+* R ⧸ span {(p : R)}) (a : k) :
    Ainf.ofWitt p f (WittVector.teichmuller p a) = Ainf.teich p (Tilt.ofPerfect p f a) := by sorry
