-- Prove2me | Theorems.Thm_Reformulated_AutPerF_wittResidueToRing_finite
-- name    : Reformulated.AutPerF.wittResidueToRing_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:18.184068+00:00
-- url     : https://prove2.me/theorems/07f2fa1f-9cf5-517b-8ec0-1e9032685b25
-- title:
--   Aut Per F: witt Residue To Ring finite
-- statement:
--   The Aut Per F construction uses the witt Residue To Ring finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L140-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L140-L170

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

theorem Reformulated.AutPerF.wittResidueToRing_finite : (wittResidueToRing p A).Finite := by sorry
