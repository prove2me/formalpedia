-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_section_algebraMap
-- name    : Reformulated.AutPerF.BdRPlus.section_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:05.674154+00:00
-- url     : https://prove2.me/theorems/0e346039-7b10-4f52-9ead-9e1e1185c944
-- title:
--   Bd RPlus: section algebra Map
-- statement:
--   The Bd RPlus construction uses the section algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L275-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L275-L280

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
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
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)]
variable [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.BdRPlus
variable {p}
variable {F : Type v} {L : Type w} [CommRing F] [CommRing L] [Algebra F L]

theorem Reformulated.AutPerF.BdRPlus.section_algebraMap [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (a : F) :
    «section» hθ ι j hj (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a) := by sorry
