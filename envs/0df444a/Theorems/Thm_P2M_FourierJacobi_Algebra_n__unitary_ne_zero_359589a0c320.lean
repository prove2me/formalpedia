-- Prove2me | Theorems.Thm_P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
-- name    : P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:08.826356+00:00
-- url     : https://prove2.me/theorems/6e09a151-49f6-42fe-b3da-b791c9a8f1cc
-- title:
--   P2 M Fourier Jacobi Algebra n  unitary ne zero 359589a0c320: P2 M Fourier Jacobi Algebra n  unitary ne zero 359589a0c320
-- statement:
--   The P2 M Fourier Jacobi Algebra n  unitary ne zero 359589a0c320 construction uses the P2 M Fourier Jacobi Algebra n  unitary ne zero 359589a0c320 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L40-L52
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/UnitaryFinite.lean#L40-L52

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra

theorem P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320 {t : ℝ} {a b : ℂ}
    (ht₀ : 0 ≤ t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    n₂ (t : ℂ) a b ≠ 0 := by sorry

alias «FourierJacobi».«Algebra».«n₂_unitary_ne_zero» := P2M_FourierJacobi_Algebra_n__unitary_ne_zero_359589a0c320
