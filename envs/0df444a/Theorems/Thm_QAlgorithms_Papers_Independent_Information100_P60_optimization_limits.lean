-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_optimization_limits
-- name    : QAlgorithms.Papers.Independent.Information100.P60.optimization_limits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:32:13.765152+00:00
-- url     : https://prove2.me/theorems/63d5cb9c-fd17-494c-8541-1c1e711fa3c4
-- title:
--   Lemma 1: optimizing before liminf or limsup
-- statement:
--   Let $Y$ be a nonempty type and $f:Y\times\mathbb N\to\mathbb R$. Embed all values in the extended real line before taking suprema and limits. Then $$\sup_{y\in Y}\liminf_{n\to\infty}f(y,n)\le\liminf_{n\to\infty}\sup_{y\in Y}f(y,n),\qquad \sup_{y\in Y}\limsup_{n\to\infty}f(y,n)\le\limsup_{n\to\infty}\sup_{y\in Y}f(y,n).$$ No boundedness assumption is imposed. These inequalities justify moving a fixed choice outside the asymptotic optimization.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 7, Lemma 1: optimizing before liminf or limsup

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF p.7, Lemma 1, both inequalities (12)–(13).
Real f is embedded in extended reals BEFORE suprema and limits. -/
theorem optimization_limits {Y : Type*} [Nonempty Y] (f : Y → ℕ → ℝ) :
    (⨆ y, liminf (fun n => (f y n : EReal)) atTop) ≤
      liminf (fun n => ⨆ y, (f y n : EReal)) atTop ∧
    (⨆ y, limsup (fun n => (f y n : EReal)) atTop) ≤
      limsup (fun n => ⨆ y, (f y n : EReal)) atTop := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
