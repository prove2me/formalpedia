-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P16_proposition3_15
-- name    : QAlgorithms.Papers.Independent.Next46.P16.proposition3_15
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:09:56.734295+00:00
-- url     : https://prove2.me/theorems/e1b4468d-ea5f-4e62-a25d-741c298cc577
-- title:
--   Positive square roots preserve Schwartz operators
-- statement:
--   Fix $N\ge1$. If $T$ is a positive Schwartz operator on $L^2(\mathbb R^N)$, then its canonical positive square root satisfies
--   $$
--   \sqrt T\in\mathcal S(\mathcal H).
--   $$
--   Positivity includes self-adjointness, and $T=0$ is permitted. No trace-one condition is imposed. The result supplies a regular positive square root within the same Schwartz class.
-- source:
--   Schwartz operators, arXiv:1503.04086v1, PDF p. 19, Proposition 3.15

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P16

noncomputable section

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration)

open QAlgorithms.Papers.Independent.Dependency50.P13 (IsTraceClass)

open scoped BigOperators ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P16

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalComplexCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealCalculus

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P16.canonicalRealNonUnitalCalculus

/-- Proposition 3.15, PDF p.19: the canonical positive square root is a
Schwartz operator. Positivity includes self-adjointness, and zero is allowed. -/
theorem proposition3_15 (n : ℕ) (hn : 0 < n) (T : CanonicalOperator n)
    (hT : IsSchwartzOperator T) (hpos : T.IsPositive) :
    IsSchwartzOperator (CFC.sqrt T) := by sorry

end QAlgorithms.Papers.Independent.Next46.P16

end
