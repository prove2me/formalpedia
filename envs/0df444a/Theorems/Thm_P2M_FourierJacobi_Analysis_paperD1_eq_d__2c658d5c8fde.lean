-- Prove2me | Theorems.Thm_P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde
-- name    : P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:18:16.380517+00:00
-- url     : https://prove2.me/theorems/34a30a52-112a-4477-a41d-f59c28bb42ee
-- title:
--   P2 M Fourier Jacobi Analysis paper D1 eq d  2c658d5c8fde: P2 M Fourier Jacobi Analysis paper D1 eq d  2c658d5c8fde
-- statement:
--   The P2 M Fourier Jacobi Analysis paper D1 eq d  2c658d5c8fde construction uses the P2 M Fourier Jacobi Analysis paper D1 eq d  2c658d5c8fde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L18-L23
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L18-L23

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde (q : ℝ) (a b d : ℂ) :
    paperD1 q a b d = d₁ (inverseSqrt q : ℂ) a b d := by sorry

alias «FourierJacobi».«Analysis».«paperD1_eq_d₁» := P2M_FourierJacobi_Analysis_paperD1_eq_d__2c658d5c8fde
