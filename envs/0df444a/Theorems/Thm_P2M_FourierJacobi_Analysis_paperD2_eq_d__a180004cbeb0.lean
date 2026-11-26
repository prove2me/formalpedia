-- Prove2me | Theorems.Thm_P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
-- name    : P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:32.152934+00:00
-- url     : https://prove2.me/theorems/cc638f40-30d0-4a79-a0e3-dba7cd9daa9b
-- title:
--   P2 M Fourier Jacobi Analysis paper D2 eq d  a180004cbeb0: P2 M Fourier Jacobi Analysis paper D2 eq d  a180004cbeb0
-- statement:
--   The P2 M Fourier Jacobi Analysis paper D2 eq d  a180004cbeb0 construction uses the P2 M Fourier Jacobi Analysis paper D2 eq d  a180004cbeb0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L25-L30
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/PaperDomain.lean#L25-L30

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0 (q : ℝ) (a b d : ℂ) :
    paperD2 q a b d = d₂ (inverseSqrt q : ℂ) a b d := by sorry

alias «FourierJacobi».«Analysis».«paperD2_eq_d₂» := P2M_FourierJacobi_Analysis_paperD2_eq_d__a180004cbeb0
