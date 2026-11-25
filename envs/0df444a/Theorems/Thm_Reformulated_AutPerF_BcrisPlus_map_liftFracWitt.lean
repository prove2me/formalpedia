-- Prove2me | Theorems.Thm_Reformulated_AutPerF_BcrisPlus_map_liftFracWitt
-- name    : Reformulated.AutPerF.BcrisPlus.map_liftFracWitt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:34:25.83791+00:00
-- url     : https://prove2.me/theorems/55978c15-77b4-5d5f-9e15-211bb6438f62
-- title:
--   Bcris Plus: map lift Frac Witt
-- statement:
--   The Bcris Plus construction uses the map lift Frac Witt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Coefficients.lean#L30-L35

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Coefficients
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_liftFracWitt

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
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {k : Type w} [Field k] [CharP k p] [PerfectRing k p]
variable {p}

theorem Reformulated.AutPerF.BcrisPlus.map_liftFracWitt (e : R →+* S) (g : WittVector p k →+* R)
    (x : FractionRing (WittVector p k)) :
    BcrisPlus.map p e (BcrisPlus.liftFracWitt p g x) = BcrisPlus.liftFracWitt p (e.comp g) x := by sorry
