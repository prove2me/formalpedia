-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_upsilon_geometric_composition
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.upsilon_geometric_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:58:32.443983+00:00
-- url     : https://prove2.me/theorems/5e8d43b8-e865-4612-bc80-9e7965ff9d3f
-- title:
--   Proposition 16 (Subadditivity)
-- statement:
--   Let $N_1,N_2$ be composable bipartite CPTP channels, and let $\alpha\in(0,1)\cup(1,2]$. All comparison maps in $\widehat\Upsilon_\alpha$ are arbitrary CP maps satisfying $\beta\le1$.
--
--   $$
--   \widehat\Upsilon_\alpha(N_2\circ N_1)\le\widehat\Upsilon_\alpha(N_2)+\widehat\Upsilon_\alpha(N_1).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 10, Proposition 16 (Subadditivity)

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

/-- Proposition 16 (Subadditivity), arXiv:2010.01058v3, PDF pp.10.
 -/
theorem upsilon_geometric_composition {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    (N1 : Superop (A × B) (C × D)) (N2 : Superop (C × D) (E × F))
    (h1 : IsChannel N1) (h2 : IsChannel N2)
    (alpha : ℝ) (halpha : (0 < alpha ∧ alpha < 1) ∨ (1 < alpha ∧ alpha ≤ 2)) :
    upsilon (geometricD alpha) (N2 ∘ N1) ≤
      upsilon (geometricD alpha) N2 + upsilon (geometricD alpha) N1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
