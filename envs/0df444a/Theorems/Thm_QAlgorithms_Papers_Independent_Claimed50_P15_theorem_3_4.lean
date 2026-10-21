-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_theorem_3_4
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.theorem_3_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:45:51.432885+00:00
-- url     : https://prove2.me/theorems/ba0bc738-a39c-4efa-a459-6dc7bb1b8069
-- title:
--   Theorem 3.4
-- statement:
--   For faithful positive functionals $(\nu_n,\omega_n)$ on possibly varying nonzero finite-dimensional systems, fix positive $w_n\to\infty$. Assume AF1: the finite limit $e(s)=\lim_n w_n^{-1}\log\operatorname{Tr}(\nu_n^s\omega_n^{1-s})$ exists on $[0,1]$, is continuous there and differentiable on $(0,1)$, and $D_+e(0)<D_-e(1)$. If $D_n$ is the minimal sum of projection-testing errors, then
--
--   $$\liminf_n w_n^{-1}\log D_n=\limsup_n w_n^{-1}\log D_n=\inf_{s\in[0,1]}e(s).$$
--
--   This Chernoff bound includes unnormalized faithful positive functionals.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 14, Theorem 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3.4 (Chernoff), arXiv:1109.3804v2, PDF p.14.
This precedes the source's normalization restriction. -/
theorem theorem_3_4 (F : FiniteTestingFamily) (e : ℝ → ℝ) (hAF1 : HasAF1 F e) :
    Filter.liminf (symmetricRate F false) atTop = sInf ((fun s => (e s : EReal)) '' Set.Icc (0 : ℝ) 1) ∧
    Filter.limsup (symmetricRate F false) atTop = sInf ((fun s => (e s : EReal)) '' Set.Icc (0 : ℝ) 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
