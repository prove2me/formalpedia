-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_ker_eval
-- name    : Reformulated.AutPerF.BdRPlus.ker_eval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:03.694342+00:00
-- url     : https://prove2.me/theorems/92873911-2359-4040-bf9a-91307cf14121
-- title:
--   Bd RPlus: ker eval
-- statement:
--   The Bd RPlus construction uses the ker eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRham.lean#L120-L123

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

theorem Reformulated.AutPerF.BdRPlus.ker_eval (n : ℕ) : RingHom.ker (eval p R n) = fil p R n := by sorry
