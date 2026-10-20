-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_composition
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:52:40.539992+00:00
-- url     : https://prove2.me/theorems/d14e9533-d74d-4fea-9f8e-0c8ea84cd5b8
-- title:
--   Proposition 6 (Subadditivity under composition)
-- statement:
--   Let $M_1:AB\to A'B'$ and $M_2:A'B'\to A''B''$ be composable completely positive maps. No normalization or trace bound is imposed.
--
--   $$
--   C_\beta(M_2\circ M_1)\le C_\beta(M_2)+C_\beta(M_1).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** Extended logarithms include C_beta(0)=-infinity; finite-dimensional beta is finite for CP maps.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 7, Proposition 6 (Subadditivity under composition)

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

/-- Proposition 6 (Subadditivity under composition), arXiv:2010.01058v3, PDF pp.7,8.
Extended logarithms include C_beta(0)=-infinity; finite-dimensional beta is finite for CP maps. -/
theorem cBeta_composition {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    (M1 : Superop (A × B) (C × D)) (M2 : Superop (C × D) (E × F))
    (h1 : CP M1) (h2 : CP M2) :
    cBeta (M2 ∘ M1) ≤ cBeta M2 + cBeta M1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
