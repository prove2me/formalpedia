-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r23b_PositivityTheory_Rg_Sw_Glob_DCalcDH_poly_exp
-- name    : UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:12.46682+00:00
-- url     : https://prove2.me/theorems/baf35291-0b19-5aad-9e68-24c6befd6729
-- title:
--   DCalc DH: poly exp
-- statement:
--   The DCalc DH construction uses the poly exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowMulExpLeHalfExp.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowMulExpLeHalfExp.lean#L36-L39

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowMulExpLeHalfExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r23b

theorem UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by sorry
