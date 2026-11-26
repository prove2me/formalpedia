-- Prove2me | Theorems.Thm_Reformulated_AutPerF_adicLift_algebraMap
-- name    : Reformulated.AutPerF.adicLift_algebraMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:06.728919+00:00
-- url     : https://prove2.me/theorems/7ddd3612-6dbd-4dd5-ae1c-e3a5672c42ab
-- title:
--   Aut Per F: adic Lift algebra Map
-- statement:
--   The Aut Per F construction uses the adic Lift algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L257-L260

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
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
variable {A Q : Type*} [CommRing A] [CommRing Q]

theorem Reformulated.AutPerF.adicLift_algebraMap (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) (a : A) :
    adicLift p g (algebraMap A _ a) = g a := by sorry
