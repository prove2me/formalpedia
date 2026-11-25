-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_hom_ext_of_formallyUnramified
-- name    : Reformulated.AutPerF.BdRPlus.hom_ext_of_formallyUnramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:46.107365+00:00
-- url     : https://prove2.me/theorems/3ac692e3-84a0-4366-b80a-2faba79cfd24
-- title:
--   Bd RPlus: hom ext of formally Unramified
-- statement:
--   The Bd RPlus construction uses the hom ext of formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L231-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L231-L240

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

theorem Reformulated.AutPerF.BdRPlus.hom_ext_of_formallyUnramified [Algebra.FormallyUnramified F L] {s₁ s₂ : L →+* BdRPlus p R}
    (hF : ∀ a : F, s₁ (algebraMap F L a) = s₂ (algebraMap F L a))
    (hθ : ∀ x, theta p R (s₁ x) = theta p R (s₂ x)) : s₁ = s₂ := by sorry
