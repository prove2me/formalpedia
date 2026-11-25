-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BcrisPlus_liftFracWitt_algebraMap
-- name    : Reformulated.AutPerF.BcrisPlus.liftFracWitt_algebraMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:51.617237+00:00
-- url     : https://prove2.me/theorems/30e89894-bed3-5625-8b5f-81f62d64f7ef
-- title:
--   Bcris Plus: lift Frac Witt algebra Map
-- statement:
--   The Bcris Plus construction uses the lift Frac Witt algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.BcrisPlus.liftFracWitt_algebraMap (g : WittVector p k →+* R) (a : WittVector p k) :
    BcrisPlus.liftFracWitt p g (algebraMap _ _ a) =
      algebraMap (Acris p R) _ (algebraMap (Ainf p R) _ (Ainf.liftWitt p g a)) := by sorry
