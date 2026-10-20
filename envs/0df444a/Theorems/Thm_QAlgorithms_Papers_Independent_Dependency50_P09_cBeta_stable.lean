-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_stable
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_stable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:49:56.630014+00:00
-- url     : https://prove2.me/theorems/9c616f39-f34b-4910-94ee-3f75d99c8062
-- title:
--   Proposition 3 (Stability)
-- statement:
--   Let $M:AB\to A'B'$ be any completely positive map, without a trace constraint. Let $E,F$ be arbitrary positive-dimensional local identity ancillas.
--
--   $$
--   C_\beta(\operatorname{id}_E\otimes M\otimes\operatorname{id}_F)=C_\beta(M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 5, Proposition 3 (Stability)

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

/-- Proposition 3 (Stability), arXiv:2010.01058v3, PDF pp.5,6.
 -/
theorem cBeta_stable {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    (M : Superop (A × B) (C × D)) (hM : CP M) :
    cBeta (stableMap (E := E) (F := F) M) = cBeta M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
