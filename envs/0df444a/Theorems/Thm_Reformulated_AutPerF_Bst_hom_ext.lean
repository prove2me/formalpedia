-- Prove2me | Theorems.Thm_Reformulated_AutPerF_Bst_hom_ext
-- name    : Reformulated.AutPerF.Bst.hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:23.830689+00:00
-- url     : https://prove2.me/theorems/f9591dbd-e129-4ad7-938f-8d9c410becbf
-- title:
--   Bst: hom ext
-- statement:
--   The Bst construction uses the hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L364-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/TruncLogEqOfPowEqZero.lean#L364-L367

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
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
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Bst
variable {p R}

theorem Reformulated.AutPerF.Bst.hom_ext {B : Type*} [CommRing B] {f g : Bst p R →+* B}
    (h₁ : ∀ x : Bcris p R, f (algebraMap _ _ x) = g (algebraMap _ _ x))
    (h₂ : ∀ ϖ, f (logFlat ϖ) = g (logFlat ϖ)) : f = g := by sorry
