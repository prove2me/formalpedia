-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_fDiv_tv_sharp
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.fDiv_tv_sharp
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:30:09.652998+00:00
-- url     : https://prove2.me/theorems/5fc5f4dc-30c1-4551-8820-6153c0335c7f
-- title:
--   Theorem 5: Sup Df(P||Q)/TV=(f(0)+f*(0))/2 over P≪Q,P!=Q
-- statement:
--   Let $f$ be convex on $(0,\infty)$ with $f(1)=0$. Write $f(0)=\lim_{t\downarrow0}f(t)$ and $f^*(0)=\lim_{t\downarrow0}t f(1/t)$. The least universal coefficient in
--
--   $$D_f(P\|Q)\le C|P-Q|,\qquad P\ll Q,$$
--
--   is $C=[f(0)+f^*(0)]/2$, with infinite endpoints allowed. The comparison ranges over all probability spaces. This expresses the supremum in Theorem 5 without an infinite-over-infinite quotient.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 21, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 5: Sup Df(P||Q)/TV=(f(0)+f*(0))/2 over P≪Q,P!=Q. Sason--Verdu, arXiv:1508.00335v7, PDF p.21.  -/
theorem fDiv_tv_sharp
    (f : ℝ → ℝ) (hf : Generator f) :
    Sharp (nDiv f) fullVariation acPairs ((generatorAtZero f + generatorAtZero (generatorConjugate f)).toENNReal / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
