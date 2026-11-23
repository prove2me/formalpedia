-- Prove2me | Theorems.Thm_Reformulated_AutPerF_AinfInv_algebraMap_away_injective
-- name    : Reformulated.AutPerF.AinfInv.algebraMap_away_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:28.493458+00:00
-- url     : https://prove2.me/theorems/1a124d89-41da-4307-ba03-7de29158493b
-- title:
--   Ainf Inv: algebra Map away injective
-- statement:
--   The Ainf Inv construction uses the algebra Map away injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L459-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean#L459-L462

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
open Reformulated.AutPerF.AinfInv
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] [ValuationRing R]

theorem Reformulated.AutPerF.AinfInv.algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) := by sorry
