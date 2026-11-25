-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BcrisPlus_algebraMap_injective
-- name    : Reformulated.AutPerF.BcrisPlus.algebraMap_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:42.572536+00:00
-- url     : https://prove2.me/theorems/81855aed-d493-502f-a034-edd3a565090e
-- title:
--   Bcris Plus: algebra Map injective
-- statement:
--   The Bcris Plus construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/EqZeroOfPMulEqZero.lean#L248-L250

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero
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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BcrisPlus

theorem Reformulated.AutPerF.BcrisPlus.algebraMap_injective : Function.Injective (algebraMap (Acris p R) (BcrisPlus p R)) := by sorry
