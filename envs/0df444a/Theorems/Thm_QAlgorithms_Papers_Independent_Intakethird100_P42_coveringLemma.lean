-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_coveringLemma
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.coveringLemma
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:10:32.599698+00:00
-- url     : https://prove2.me/theorems/0ad8bf0d-1a7f-4be3-811f-a98e450a60f1
-- title:
--   Lemma 3.5: covering lemma
-- statement:
--   Let $X,Y$ be finite nonempty alphabets, $q$ a probability distribution on $Y$, and $P(\cdot\mid y)$ a probability distribution on $X$ for every $y$. Put $p(x)=\sum_yq(y)P(x\mid y)$. Suppose $\epsilon,K,k>0$, $0<\eta<1$, $T\subseteq X$, and $T_y\subseteq X$ satisfy
--   $$\sum_yq(y)P(T_y\mid y)\ge1-\epsilon,\quad p(T)\ge1-\epsilon,\quad |T|\le K,\quad P(x\mid y)\le k^{-1}\quad(x\in T_y).$$
--   Let $M=\lceil K/(\eta k)\rceil$ and independently sample $D(1),\ldots,D(M)$ from $q$. There is an absolute constant $\kappa>0$ and a selection, for every whole book $D$, of a normalized conditional distribution $E_D(i\mid x)$ on $[M]$ such that
--   $$\Pr_D\!\left\{\sum_{i=1}^M\sum_x\left|\frac{P(x\mid D(i))}{M}-p(x)E_D(i\mid x)\right|\ge5\epsilon\right\}\le2K\exp(-\kappa\epsilon^3/\eta).$$
--   The constant is uniform over the data. Every encoder row is normalized, including when $p(x)=0$; selection may depend on the sampled book.
--
--   This compares the entire joint distribution on $[M]\times X$ in the dilution and concentration directions. The printed proof's subnormalized completion step is flagged for moderation; it is not added as a hypothesis.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 7, Lemma 3.5: covering lemma

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.7--9, Lemma 3.5: covering, including the ceiling, normalized encoder
and full joint l1 norm. The encoder can depend on the entire sampled book;
its selection is outside the event, not an assumption that a good encoder exists. -/
theorem coveringLemma :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (X Y : Type) [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
        (q : Y → ℝ) (P : Y → X → ℝ),
        IsProbability q → (∀ y, IsProbability (P y)) →
        ∀ (T : Finset X) (Ty : Y → Finset X) (eps K k eta : ℝ),
          0 < eps → 0 < K → 0 < k → 0 < eta → eta < 1 →
          (1 - eps ≤ ∑ y, q y * ∑ x ∈ Ty y, P y x) →
          (1 - eps ≤ ∑ y, q y * ∑ x ∈ T, P y x) →
          (T.card : ℝ) ≤ K → (∀ y x, x ∈ Ty y → P y x ≤ k⁻¹) →
          let M := ⌈K / (eta * k)⌉₊
          ∃ select : (Fin M → Y) → CoverEncoder X M,
            (∑ book : Fin M → Y,
              if 5 * eps ≤ coveringError q P M book (select book) then ∏ i, q (book i)
              else 0) ≤ 2 * K * Real.exp (-kappa * eps ^ 3 / eta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
