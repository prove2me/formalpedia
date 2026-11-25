-- Prove2me | Theorems.Thm_Reformulated_AutPerF_modPToResidue_residueSection
-- name    : Reformulated.AutPerF.modPToResidue_residueSection
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:13.137001+00:00
-- url     : https://prove2.me/theorems/79a2adfb-b299-5cc9-8a60-3500b79e760b
-- title:
--   Aut Per F: mod PTo Residue residue Section
-- statement:
--   The Aut Per F construction uses the mod PTo Residue residue Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L89-L96

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
variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]

theorem Reformulated.AutPerF.modPToResidue_residueSection (a : ResidueField A) :
    modPToResidue p A (residueSection p A a) = a := by sorry
