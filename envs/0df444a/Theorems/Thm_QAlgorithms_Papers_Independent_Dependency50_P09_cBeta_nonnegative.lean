-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_cBeta_nonnegative
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.cBeta_nonnegative
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:49:00.032591+00:00
-- url     : https://prove2.me/theorems/e0b8e4a5-1a8c-4190-b310-33795b2f9b3a
-- title:
--   Proposition 2 (Non-negativity)
-- statement:
--   Let $N:AB\to A'B'$ be a channel on finite systems of positive dimensions. Write $\beta$ for the Choi optimization (16), and $C_\beta=\log_2\beta$.
--
--   $$
--   C_\beta(N)\ge 0.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 5, Proposition 2 (Non-negativity)

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

/-- Proposition 2 (Non-negativity), arXiv:2010.01058v3, PDF pp.5.
 -/
theorem cBeta_nonnegative {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (N : Superop (A × B) (C × D)) (hN : IsChannel N) :
    0 ≤ cBeta N := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
