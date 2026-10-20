-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_perspectiveTensor_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.perspectiveTensor_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:11:51.544981+00:00
-- url     : https://prove2.me/theorems/089f7e06-8364-4fb1-b86f-8afef6e99c77
-- title:
--   Lemma 17: operator convexity of the perspective tensor
-- statement:
--   For $\alpha\in[1,2]$, $\beta\in[0,1]$, $L\ge0$, and $R>0$, define
--
--   $$
--   F(L,R)=R^{\beta/2}(R^{-\beta/2}LR^{-\beta/2})^\alpha R^{\beta/2}\otimes(R^T)^{(1-\alpha)(1-\beta)}.
--   $$
--
--   For any two such pairs and $\lambda\in[0,1]$,
--
--   $$
--   F(\lambda L_1+(1-\lambda)L_2,\lambda R_1+(1-\lambda)R_2)\le\lambda F(L_1,R_1)+(1-\lambda)F(L_2,R_2)
--   $$
--
--   in the Loewner order. Only the inner sandwich has exponent $\alpha$; no trace normalization is assumed. This is the operator-perspective convexity needed by the divergence argument.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 22, Lemma 17

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.22, Lemma 17: R is positive definite, L only PSD; both alpha and beta
endpoints are included, without any trace normalization. -/
theorem perspectiveTensor_convex {I : Type} [Fintype I] [DecidableEq I]
    (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 1)
    (L1 L2 R1 R2 : Mat I) (hL1 : L1.PosSemidef) (hL2 : L2.PosSemidef)
    (hR1 : R1.PosDef) (hR2 : R2.PosDef) (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
    (((l : ℂ) • perspectiveTensor a b L1 R1 + ((1-l : ℝ) : ℂ) • perspectiveTensor a b L2 R2) -
      perspectiveTensor a b ((l : ℂ) • L1 + ((1-l : ℝ) : ℂ) • L2)
        ((l : ℂ) • R1 + ((1-l : ℝ) : ℂ) • R2)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
