-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_localProduct
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_localProduct
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:51:38.651487+00:00
-- url     : https://prove2.me/theorems/64299fda-961c-4036-ab00-bb6a2511a6ff
-- title:
--   Proposition 5 (Zero on tensor product of local channels)
-- statement:
--   Let $E:A\to A'$ and $F:B\to B'$ be arbitrary local CPTP channels on finite positive-dimensional systems.
--
--   $$
--   C_\beta(E\otimes F)=0.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 6, Proposition 5 (Zero on tensor product of local channels)

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

/-- Proposition 5 (Zero on tensor product of local channels), arXiv:2010.01058v3, PDF pp.6.
 -/
theorem cBeta_localProduct {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (E : Superop A C) (F : Superop B D) (hE : IsChannel E) (hF : IsChannel F) :
    cBeta (tensorAction E F) = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
