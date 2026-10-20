-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_beta_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.beta_convex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:55:34.881516+00:00
-- url     : https://prove2.me/theorems/847885ad-2923-45dd-9ea3-beb76bee1cd9
-- title:
--   Proposition 9 (Convexity)
-- statement:
--   Let $M_0,M_1$ be CP maps on the same bipartite ports, and let $\lambda\in[0,1]$. Convexity concerns $\beta$ itself.
--
--   $$
--   \beta(\lambda M_1+(1-\lambda)M_0)\le\lambda\beta(M_1)+(1-\lambda)\beta(M_0).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 8, Proposition 9 (Convexity)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 9 (Convexity), arXiv:2010.01058v3, PDF pp.8.
 -/
theorem beta_convex {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (M0 M1 : Superop (A × B) (C × D)) (h0 : CP M0) (h1 : CP M1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    bipartiteBeta (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X) ≤
      (lam : EReal) * bipartiteBeta M1 + ((1-lam : ℝ) : EReal) * bipartiteBeta M0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
