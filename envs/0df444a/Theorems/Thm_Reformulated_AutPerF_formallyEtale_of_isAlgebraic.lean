-- Prove2me | Theorems.Thm_Reformulated_AutPerF_formallyEtale_of_isAlgebraic
-- name    : Reformulated.AutPerF.formallyEtale_of_isAlgebraic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:57.8957+00:00
-- url     : https://prove2.me/theorems/96bf6661-18bf-466d-960f-8136319c5e7a
-- title:
--   Aut Per F: formally Etale of is Algebraic
-- statement:
--   The Aut Per F construction uses the formally Etale of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L294-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L294-L296

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
variable [IsAdicComplete (span {(p : R)}) R]

theorem Reformulated.AutPerF.formallyEtale_of_isAlgebraic (F : Type v) (L : Type w) [Field F] [Field L] [Algebra F L]
    [CharZero F] [Algebra.IsAlgebraic F L] : Algebra.FormallyEtale F L := by sorry
