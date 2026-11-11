-- Prove2me | Theorems.Thm_PriceIgnorance_Pairwise_fact_2_3
-- name    : PriceIgnorance.Pairwise.fact_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:12:34.203506+00:00
-- url     : https://prove2.me/theorems/db797daf-07fd-4e5e-bdf8-b11b86094120
-- title:
--   Fact 2.3 — $k$-wise independence passes to $k-1$, to coordinatewise functions, and to concatenations of independent vectors
-- statement:
--   Let $(\Omega,\mathbb P)$ be a probability space and $X=(X_1,\dots,X_a)$, $Y=(Y_1,\dots,Y_b)$ random real vectors that are both $k$-wise independent. Then:
--
--   1. $X$ is $(k-1)$-wise independent;
--   2. for all measurable $f_1,\dots,f_a:\mathbb R\to\mathbb R$, the vector $(f_1(X_1),\dots,f_a(X_a))$ is $k$-wise independent;
--   3. if $X$ and $Y$ are independent of each other, the concatenation
--   $$X_1,\dots,X_a,Y_1,\dots,Y_b$$
--   is $k$-wise independent.
--
--   These closure properties are used to transfer pairwise independence through the discretization of Lemma 3.3 and through the padding construction of Theorem 3.16.
--
--   Differences from the source:
--   - encoding: random real vectors X, Y → families of measurable maps Ω → ℝ indexed by Fin a, Fin b on a probability space; reason: a random vector is a measurable map; 0-based indices
--   - reading: any deterministic functions f_i : R → R → measurable f_i : ℝ → ℝ; reason: f_i(X_i) must be a random variable; the proof (p. 23) uses P[X_i ∈ f_i^{-1}(A_i)] for Borel A_i
--   - encoding: (k − 1)-wise independence → KWiseIndep with natural-number k - 1; reason: at k = 0 Lean's k - 1 = 0, and 0-wise independence is trivially true; all k ≥ 1 are unchanged
--   - encoding: X and Y independent of each other; the concatenated vector → IndepFun of the vector-valued maps ω ↦ X(ω), ω ↦ Y(ω); concatenation by Fin.append; reason: the same notions in Lean
-- source:
--   Abdallah, Wajc, Price of Ignorance in Pairwise-Independent Prophet Inequalities, STOC 2027 submission (manuscript sha256 c79626fd…), p. 4, Fact 2.3 (proof p. 23)

import Mathlib
import Definitions.Def_LaconicBarrier_KWiseIndep

open MeasureTheory ProbabilityTheory

namespace PriceIgnorance.Pairwise

/-- Fact 2.3 (p. 4): if the random real vectors `X = (X_1, …, X_a)` and `Y = (Y_1, …, Y_b)` are
both `k`-wise independent, then (1) `X` is `(k - 1)`-wise independent; (2) `(f_1(X_1), …, f_a(X_a))`
is `k`-wise independent for all (measurable) `f_i : ℝ → ℝ`; (3) the concatenation
`X_1, …, X_a, Y_1, …, Y_b` is `k`-wise independent if `X` and `Y` are independent. -/
theorem fact_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {a b : ℕ} (X : Fin a → Ω → ℝ) (Y : Fin b → Ω → ℝ) (k : ℕ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hX : LaconicBarrier.KWiseIndep μ X k) (hY : LaconicBarrier.KWiseIndep μ Y k) :
    LaconicBarrier.KWiseIndep μ X (k - 1) ∧
    (∀ f : Fin a → ℝ → ℝ, (∀ i, Measurable (f i)) →
      LaconicBarrier.KWiseIndep μ (fun i ω => f i (X i ω)) k) ∧
    (IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) μ →
      LaconicBarrier.KWiseIndep μ
        (fun t ω => Fin.append (fun i => X i ω) (fun j => Y j ω) t) k) := by sorry

end PriceIgnorance.Pairwise
