-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdR_algebraMap_mem_fil_iff
-- name    : Reformulated.AutPerF.BdR.algebraMap_mem_fil_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:09.490239+00:00
-- url     : https://prove2.me/theorems/d604c066-7714-55dc-9a35-34175a08978f
-- title:
--   Bd R: algebra Map mem fil iff
-- statement:
--   The Bd R construction uses the algebra Map mem fil iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L331-L334

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
open Reformulated.AutPerF.BdR
variable [IsAlgClosed (FractionRing R)]

theorem Reformulated.AutPerF.BdR.algebraMap_mem_fil_iff (n : ℕ) (x : BdRPlus p R) :
    algebraMap _ (BdR p R) x ∈ fil p R n ↔ x ∈ BdRPlus.fil p R n := by sorry
