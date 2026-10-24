-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_twoProductReduction
-- name    : QAlgorithms.Papers.Independent.Information100.P21.twoProductReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:56:03.375689+00:00
-- url     : https://prove2.me/theorems/6777de58-65fe-43fd-80e5-9441d290fcef
-- title:
--   VI.16 — Proposition VI.16 (Two-product reduction). Suppose that ρX lies in the w-entangled branch, |w|2 > bc. For every
-- statement:
--   For a physical canonical X state in the $w$-entangled branch $w^2>bc$, every positive noise $N$ with separable unnormalized target can be replaced by
--   $$N'=u|01\rangle\langle01|+v|10\rangle\langle10|,\quad u,v\ge0,\quad\operatorname{Tr}N'=\operatorname{Tr}N,$$
--   while retaining target separability. The replacement noise is separable. At least one generalized and standard optimum has this support. In the $z$-entangled branch, replace the pair by $|00\rangle,|11\rangle$. The claim is universal over feasible $N$, not a support assertion about every original optimizer.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 19, VI.16 — Proposition VI.16 (Two-product reduction). Suppose that ρX lies in the w-entangled branch, |w|2 > bc. For every

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 19, Proposition VI.16 (Two-product reduction). Suppose that ρX lies in the w-entangled branch, |w|2 > bc. For every. -/
theorem twoProductReduction (a b c d w z : ℝ) (h : physicalX a b c d w z) :
  ∀ odd : Bool, (if odd then b*c<w^2 else a*d<z^2) →
  (∀ N : Op QQ, N.PosSemidef → QAlgorithms.Entanglement.IsSeparablePositive (xstate a b c d w z+N) →
    ∃ u v : ℝ, 0≤u ∧ 0≤v ∧ QAlgorithms.Entanglement.IsSeparablePositive (compressed odd u v) ∧
      (compressed odd u v).trace=N.trace ∧
      QAlgorithms.Entanglement.IsSeparablePositive (xstate a b c d w z+compressed odd u v)) ∧
  (∃ u v : ℝ, 0≤u ∧ 0≤v ∧ optG (xstate a b c d w z) (compressed odd u v) ∧
    optS (xstate a b c d w z) (compressed odd u v)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
