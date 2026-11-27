-- Prove2me | Theorems.Thm_Reformulated_AutPerF_residueField_charP
-- name    : Reformulated.AutPerF.residueField_charP
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:45.982182+00:00
-- url     : https://prove2.me/theorems/68b84b11-25ce-44c9-a7be-bf8de269751a
-- title:
--   Aut Per F: residue Field char P
-- statement:
--   The Aut Per F construction uses the residue Field char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L47-L50

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
open Reformulated Reformulated.AutPerF
universe u
variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]
omit [CharZero A]

theorem Reformulated.AutPerF.residueField_charP : CharP (ResidueField A) p := by sorry
