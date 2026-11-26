-- Prove2me | Theorems.Thm_P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
-- name    : P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:40:45.546397+00:00
-- url     : https://prove2.me/theorems/5f82a8b8-8601-5af9-af8e-0d5ce51a4bcb
-- title:
--   P2 M Fourier Jacobi Algebra special negative d  9d3a998530fe: P2 M Fourier Jacobi Algebra special negative d  9d3a998530fe
-- statement:
--   The P2 M Fourier Jacobi Algebra special negative d  9d3a998530fe construction uses the P2 M Fourier Jacobi Algebra special negative d  9d3a998530fe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/EulerFactors.lean#L102-L106
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Algebra/EulerFactors.lean#L102-L106

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]

theorem P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe (t a b : K) :
    d₁ t a b (-t) = fourFactors a b (-t ^ 2) := by sorry

alias «FourierJacobi».«Algebra».«special_negative_d₁» := P2M_FourierJacobi_Algebra_special_negative_d__9d3a998530fe
