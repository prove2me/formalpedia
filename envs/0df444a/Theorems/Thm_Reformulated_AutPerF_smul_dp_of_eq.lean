-- Prove2me | Theorems.Thm_Reformulated_AutPerF_smul_dp_of_eq
-- name    : Reformulated.AutPerF.smul_dp_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:08.421807+00:00
-- url     : https://prove2.me/theorems/93240a9f-c516-4b96-8377-32c98af9433b
-- title:
--   Aut Per F: smul dp of eq
-- statement:
--   The Aut Per F construction uses the smul dp of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Envelope.lean#L101-L103

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
variable {B : Type*} [CommRing B] [Algebra ℚ B]
variable {A : Type*} [CommRing A] [Algebra A B]
variable {ξ : A}

theorem Reformulated.AutPerF.smul_dp_of_eq (m : ℕ) (c : A) : (ξ * c) • dp m (algebraMap A B ξ) =
    ((m + 1 : ℕ) : B) * (c • dp (m + 1) (algebraMap A B ξ)) := by sorry
