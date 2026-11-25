-- Prove2me | Theorems.Thm_Reformulated_AutPerF_wittResidueToRing_injective
-- name    : Reformulated.AutPerF.wittResidueToRing_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:17.171963+00:00
-- url     : https://prove2.me/theorems/e2925375-5a66-4124-8d2f-04e2550062d9
-- title:
--   Aut Per F: witt Residue To Ring injective
-- statement:
--   The Aut Per F construction uses the witt Residue To Ring injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L109-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean#L109-L116

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

theorem Reformulated.AutPerF.wittResidueToRing_injective : Function.Injective (wittResidueToRing p A) := by sorry
