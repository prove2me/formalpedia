-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_eq_section
-- name    : Reformulated.AutPerF.BdRPlus.eq_section
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:47.61532+00:00
-- url     : https://prove2.me/theorems/fc616e18-4bfc-4180-bf7e-aedfed2644d9
-- title:
--   Bd RPlus: eq section
-- statement:
--   The Bd RPlus construction uses the eq section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L282-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L282-L290

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

theorem Reformulated.AutPerF.BdRPlus.eq_section [Algebra.FormallyEtale F L]
    (hθ : Function.Surjective (AinfInv.theta p R)) (ι : F →+* AinfInv p R)
    (j : L →+* Localization.Away (p : R))
    (hj : ∀ a : F, j (algebraMap F L a) = AinfInv.theta p R (ι a)) (s : L →+* BdRPlus p R)
    (h₁ : ∀ x, theta p R (s x) = j x)
    (h₂ : ∀ a : F, s (algebraMap F L a) = algebraMap (AinfInv p R) _ (ι a)) :
    s = «section» hθ ι j hj := by sorry
