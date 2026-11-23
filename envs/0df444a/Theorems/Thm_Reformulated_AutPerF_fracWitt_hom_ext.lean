-- Prove2me | Theorems.Thm_Reformulated_AutPerF_fracWitt_hom_ext
-- name    : Reformulated.AutPerF.fracWitt_hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:26.599338+00:00
-- url     : https://prove2.me/theorems/60c9ea6c-de6f-4f0c-b037-cdbe99a957a4
-- title:
--   Aut Per F: frac Witt hom ext
-- statement:
--   The Aut Per F construction uses the frac Witt hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L137-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Section.lean#L137-L139

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
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.fracWitt_hom_ext {B : Type*} [CommRing B] {f g : FractionRing (WittVector p k) →+* B}
    (h : ∀ a : WittVector p k, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by sorry
