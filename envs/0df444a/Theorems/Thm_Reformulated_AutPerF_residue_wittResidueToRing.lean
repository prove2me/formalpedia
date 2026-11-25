-- Prove2me | Theorems.Thm_Reformulated_AutPerF_residue_wittResidueToRing
-- name    : Reformulated.AutPerF.residue_wittResidueToRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:29.128444+00:00
-- url     : https://prove2.me/theorems/5e294bb0-7402-40bf-9ded-04e0a6bc724f
-- title:
--   Aut Per F: residue witt Residue To Ring
-- statement:
--   The Aut Per F construction uses the residue witt Residue To Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L103-L107

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
variable [IsAdicComplete (span {(p : A)}) A]

theorem Reformulated.AutPerF.residue_wittResidueToRing (x : WittVector p (ResidueField A)) :
    residue A (wittResidueToRing p A x) = x.coeff 0 := by sorry
