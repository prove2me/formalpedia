-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_localProcessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_localProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:53:39.140522+00:00
-- url     : https://prove2.me/theorems/37967c3e-607f-4fe8-8899-462966f1c3f8
-- title:
--   Corollary 7 (Data processing under local channels)
-- statement:
--   Let $M$ be a bipartite CP map and let $K,L,N,P$ be CPTP local preprocessing and postprocessing channels with matching ports. All systems have positive finite dimensions.
--
--   $$
--   C_\beta((N\otimes P)\circ M\circ(K\otimes L))\le C_\beta(M).
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 8, Corollary 7 (Data processing under local channels)

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

/-- Corollary 7 (Data processing under local channels), arXiv:2010.01058v3, PDF pp.8.
 -/
theorem cBeta_localProcessing {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    {E : Type} [Fintype E] [Nonempty E]
    {F : Type} [Fintype F] [Nonempty F]
    {K : Type} [Fintype K] [Nonempty K]
    {L : Type} [Fintype L] [Nonempty L]
    (M : Superop (A × B) (C × D)) (hM : CP M)
    (preA : Superop E A) (preB : Superop F B)
    (postA : Superop C K) (postB : Superop D L)
    (hpreA : IsChannel preA) (hpreB : IsChannel preB)
    (hpostA : IsChannel postA) (hpostB : IsChannel postB) :
    cBeta (tensorAction postA postB ∘ M ∘ tensorAction preA preB) ≤ cBeta M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
