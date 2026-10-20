-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_upsilon_geometric_bounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.upsilon_geometric_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:57:48.162807+00:00
-- url     : https://prove2.me/theorems/a299ba5a-c126-4ba7-a2ce-ce4fd7fa4ca7
-- title:
--   Proposition 15
-- statement:
--   Let $N$ be a bipartite channel and $1<\alpha\le2$. Write $\widehat\Upsilon$ and $\widehat\Upsilon_\alpha$ for (161) with the Belavkin–Staszewski and geometric Rényi divergences, respectively.
--
--   $$
--   \widehat\Upsilon(N)\le\widehat\Upsilon_\alpha(N)\le C_\beta(N).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 10, Proposition 15

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

/-- Proposition 15, arXiv:2010.01058v3, PDF pp.10.
 -/
theorem upsilon_geometric_bounds {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N)
    (alpha : ℝ) (halpha : 1 < alpha ∧ alpha ≤ 2) :
    upsilon bsD N ≤ upsilon (geometricD alpha) N ∧
      upsilon (geometricD alpha) N ≤ cBeta N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
