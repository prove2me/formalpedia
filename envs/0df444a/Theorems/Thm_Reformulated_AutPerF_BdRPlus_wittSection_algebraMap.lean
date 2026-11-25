-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BdRPlus_wittSection_algebraMap
-- name    : Reformulated.AutPerF.BdRPlus.wittSection_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:49:54.654419+00:00
-- url     : https://prove2.me/theorems/c8455f6c-df56-4200-af4b-953a02f9c477
-- title:
--   Bd RPlus: witt Section algebra Map
-- statement:
--   The Bd RPlus construction uses the witt Section algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Embedding.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Embedding.lean#L177-L182

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
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
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]
variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]
variable {p O}

theorem Reformulated.AutPerF.BdRPlus.wittSection_algebraMap (g : WittVector p k →+* O) (j : L →+* C)
    (hj : ∀ a : WittVector p k,
      j (algebraMap (FractionRing (WittVector p k)) L (algebraMap _ _ a)) = g a)
    (a : FractionRing (WittVector p k)) :
    BdRPlus.wittSection g j hj (algebraMap _ L a) = algebraMap _ _ (AinfInv.liftFracWitt p g a) := by sorry
