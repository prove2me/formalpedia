-- Prove2me | Theorems.Thm_Reformulated_AutPerF_tateRoot_pow
-- name    : Reformulated.AutPerF.tateRoot_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:04.544742+00:00
-- url     : https://prove2.me/theorems/efee8c72-86b3-48e5-a732-c8bc431194ed
-- title:
--   Aut Per F: tate Root pow
-- statement:
--   The Aut Per F construction uses the tate Root pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L358-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L358-L359

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
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
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

theorem Reformulated.AutPerF.tateRoot_pow (η : tateModule p R) : tateRoot η ^ p = η.1 := by sorry
