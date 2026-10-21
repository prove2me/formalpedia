-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_rareComponent_asymptotic
-- name    : QAlgorithms.Papers.Independent.Next46.P31.rareComponent_asymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:27:53.460049+00:00
-- url     : https://prove2.me/theorems/babefe4e-3921-43be-99f3-2eed387861ed
-- title:
--   Example 2.4: skewed weighting of rare components
-- statement:
--   Let $a_m=(6/\pi^2)\sum_{r=1}^m r^{-2}$, $a_0=0$, and $\phi_m=(a_m-a_{m-1})^{-1/2}1_{[a_{m-1},a_m)}$ on $L^2(\mathbb R)$ for $m\ge1$. For positive integers $n$, define $\lambda_{n,1}=1/n$, $\lambda_{n,m}=1/n^3$ for $2\le m\le n^3-n^2+1$, and zero otherwise. Let $\rho_n=\sum_m\lambda_{n,m}|\phi_m\rangle\langle\phi_m|$. Put $a=6/\pi^2$. The spatial index, formed using the centered anticommutator, satisfies
--
--   $$
--   S_X(\rho_n)\sim\frac{\sqrt{a^2/12}}{\sqrt{a^2/12+2(a/2-1)^2}}\qquad(n\to\infty).
--   $$
--
--   This constant is the source’s final first-state moment ratio, since $\phi_1$ has mean $a/2$ and variance $a^2/12$. The limit depends on that first component even though its probability weight $1/n$ tends to zero.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 9, Example 2.4: skewed weighting of rare components

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF p.9, Example 2.4: the final asymptotic, not the intermediate
norm expansions, which each omit the same factor 2. The rare state's weight
is 1/n; 1/n^2 is its squared weight in HS formulas. No momentum regularity is
assumed for the interval indicators. The finite n=0 default is outside the limit. -/
theorem rareComponent_asymptotic {I : Type*} (b : HilbertBasis I ℂ (EuclideanSchrodinger 1)) :
    Tendsto (fun n : ℕ => coherenceIndex b positionGraph (kernelOperator (rareKernel n)) /
      rareCoefficient) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
