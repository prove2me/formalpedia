-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_beta_pointChoi
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.beta_pointChoi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:59:19.713693+00:00
-- url     : https://prove2.me/theorems/45a89859-a0bd-4a87-997b-740724ebe287
-- title:
--   Proposition 17
-- statement:
--   Let $M:A\to B'$ be any CP map, with trivial Bob input and Alice output. Let $J_M$ be its unnormalized input-first Choi operator and $T_{B'}$ the output partial transpose. Both optimization variables are Hermitian, without normalization.
--
--   $$
--   \beta(M)=\inf\{\operatorname{Tr}S:\ T_{B\prime}(V\pm J_M)\ge0,\ I_A\otimes S\pm V\ge0\}.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 10, Proposition 17

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

/-- Proposition 17, arXiv:2010.01058v3, PDF pp.10,11.
 -/
theorem beta_pointChoi {A : Type} [Fintype A] [Nonempty A]
    {D : Type} [Fintype D] [Nonempty D]
    (M : Superop A D) (hM : CP M) :
    bipartiteBeta (pointMap M) = pointBetaChoi M := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
