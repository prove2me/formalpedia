-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_algebraMap_ainf_injective
-- name    : Reformulated.AutPerF.BdRPlus.algebraMap_ainf_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:51.690663+00:00
-- url     : https://prove2.me/theorems/5ca9b71d-6848-4427-98fd-9d0c992ac268
-- title:
--   Bd RPlus: algebra Map ainf injective
-- statement:
--   The Bd RPlus construction uses the algebra Map ainf injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L240-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L240-L241

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRham
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
variable [IsDomain R] [ValuationRing R] [CharZero R]
open Reformulated.AutPerF.BdRPlus
variable [IsAlgClosed (FractionRing R)]

theorem Reformulated.AutPerF.BdRPlus.algebraMap_ainf_injective : Function.Injective (algebraMap (Ainf p R) (BdRPlus p R)) := by sorry
