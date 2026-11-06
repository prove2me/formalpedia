-- Prove2me | Theorems.Thm_P2M_OAI_SevenEighths_HeckeTheta_pair_g__560c5e067664
-- name    : P2M_OAI_SevenEighths_HeckeTheta_pair_g__560c5e067664
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:53:59.158025+00:00
-- url     : https://prove2.me/theorems/016a1490-1d19-4460-a569-641cb8719a2b
-- title:
--   P2 M OAI Seven Eighths Hecke Theta pair g  560c5e067664: P2 M OAI Seven Eighths Hecke Theta pair g  560c5e067664
-- statement:
--   The P2 M OAI Seven Eighths Hecke Theta pair g  560c5e067664 construction uses the P2 M OAI Seven Eighths Hecke Theta pair g  560c5e067664 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L138-L148
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Theta.lean#L138-L148

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem P2M_OAI_SevenEighths_HeckeTheta_pair_g__560c5e067664 {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).g₀ = 2 * dualScalar N * ∑ a, w a := by sorry

alias «OAI».«SevenEighths».«HeckeTheta».«pair_g₀» := P2M_OAI_SevenEighths_HeckeTheta_pair_g__560c5e067664
