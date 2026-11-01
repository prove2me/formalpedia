-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_iidCovering
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.iidCovering
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:11:11.29891+00:00
-- url     : https://prove2.me/theorems/44a55ad6-f515-47f2-a2e7-567f9b049cf1
-- title:
--   Corollary 3.6: IID covering
-- statement:
--   Let $q(y)P(x\mid y)$ be a probability law on finite nonempty alphabets $X,Y$, with marginal $p(x)=\sum_yq(y)P(x\mid y)$. Independently sample a book $D:[M]\to Y^n$ from $q^{\otimes n}$, for an arbitrary integer $M\ge1$. Put $P^n(x^n\mid y^n)=\prod_{j=1}^nP(x_j\mid y_j)$.
--
--   There is an absolute constant $\kappa>0$ and a constant $c>0$ depending only on this joint law such that for every $\epsilon,\delta>0$, all sufficiently large positive $n$ admit a book-dependent selection of normalized encoders $E_D(i\mid x^n)$ satisfying
--   $$\Pr_D\!\left\{\sum_{i,x^n}\left|\frac{P^n(x^n\mid D(i))}{M}-p^{\otimes n}(x^n)E_D(i\mid x^n)\right|\ge5\epsilon\right\}\le2\alpha\exp\!\left(-\frac{\kappa M\epsilon^3\beta}{\alpha}\right),$$
--   where $\alpha=2^{n[H(X)+c\delta]}$ and $\beta=2^{n[H(X\mid Y)-c\delta]}$. Entropies are in bits. The threshold is independent of $M$ and the error is the full joint $\ell^1$ norm on $[M]\times X^n$.
--
--   This is the IID joint-covering statement used to construct the stochastic encoder for channel simulation.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 9, Corollary 3.6: IID covering

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.9--10, Corollary 3.6: IID covering for every positive M. Constants
precede accuracy, blocklength and book size; alpha and beta use opposite signs. -/
theorem iidCovering :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (X Y : Type) [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
        (q : Y → ℝ) (P : Y → X → ℝ),
        IsProbability q → (∀ y, IsProbability (P y)) →
        ∃ c : ℝ, 0 < c ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
          ∀ n ≥ N, 1 ≤ n → ∀ M : ℕ, 1 ≤ M →
            let alpha := (2 : ℝ) ^ ((n : ℝ) *
              (shannon (coveringMarginal q P) + c * delta))
            let beta := (2 : ℝ) ^ ((n : ℝ) *
              ((∑ y, q y * shannon (P y)) - c * delta))
            ∃ select : (Fin M → Copies Y n) → CoverEncoder (Copies X n) M,
              bookProbability q n M (fun book => 5 * eps ≤
                coveringError (wordProb q n) (productConditional P n) M book (select book)) ≤
                  2 * alpha * Real.exp (-kappa * M * eps ^ 3 * beta / alpha) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
