-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_section
-- name    : Reformulated.AutPerF.BdRPlus.theta_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:51.8675+00:00
-- url     : https://prove2.me/theorems/7ef54d8f-9576-4acf-8997-e2be81a81485
-- title:
--   Bd RPlus: theta section
-- statement:
--   The Bd RPlus construction uses the theta section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L269-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L269-L273

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

theorem Reformulated.AutPerF.BdRPlus.theta_section [Algebra.FormallySmooth F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (x : L) :
    theta p R («section» hθ ι j hj x) = j x := by sorry
