-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_beta_composition
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.beta_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:09:32.236985+00:00
-- url     : https://prove2.me/theorems/9ad827f9-cc1b-4ea2-b09f-7e1c52a4ed8c
-- title:
--   Proposition 32
-- statement:
--   Let $M_1,M_2$ be any composable bipartite CP maps on positive-dimensional finite systems, including maps that do not preserve or decrease trace.
--
--   $$
--   \beta(M_2\circ M_1)\le\beta(M_2)\beta(M_1).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Retained as the separately numbered alternative map-form result, despite equivalence to the logarithmic Proposition 6.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 24, Proposition 32

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

/-- Proposition 32, arXiv:2010.01058v3, PDF pp.24,25.
Retained as the separately numbered alternative map-form result, despite equivalence to the logarithmic Proposition 6. -/
theorem beta_composition {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    (M1 : Superop (A × B) (C × D)) (M2 : Superop (C × D) (E × F))
    (h1 : CP M1) (h2 : CP M2) :
    bipartiteBeta (M2 ∘ M1) ≤ bipartiteBeta M2 * bipartiteBeta M1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
