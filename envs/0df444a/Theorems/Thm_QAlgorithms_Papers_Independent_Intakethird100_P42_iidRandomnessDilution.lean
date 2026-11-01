-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P42_iidRandomnessDilution
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P42.iidRandomnessDilution
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:09:54.323825+00:00
-- url     : https://prove2.me/theorems/3557589f-de4d-42a9-973d-a7ae1888dce7
-- title:
--   Corollary 3.4: IID randomness dilution
-- statement:
--   Let $q$ be a probability distribution on a finite nonempty alphabet $Y$. Independently sample a codebook $D=(Y_1,\ldots,Y_M)$ from $q^{\otimes n}$. For each fixed codebook, let $\widetilde q_D$ be the distribution of $Y_W$ when $W$ is sampled uniformly from $[M]=\{1,\ldots,M\}$ independently of that book. Thus $\widetilde q_D$ is the empirical law conditional on the book.
--
--   There is an absolute constant $\kappa>0$ and a constant $c>0$ depending only on $q$ such that, for every $\epsilon,\delta>0$, all sufficiently large positive $n$, and every integer $M\ge1$, with $\gamma=2^{n[H(q)+c\delta]}$,
--   $$\Pr_D\!\left\{\left\|q^{\otimes n}-\widetilde q_D\right\|_1\ge2\epsilon\right\}\le2\gamma\exp\!\left(-\frac{\kappa M\epsilon^2}{\gamma}\right).$$
--   The blocklength threshold is independent of $M$; Shannon entropy is in bits and the norm is the full sum of absolute differences.
--
--   This quantifies IID randomness dilution without identifying the empirical conditional law with its unconditional average.
-- source:
--   Channel simulation with quantum side information, arXiv:quant-ph/0611008v1, PDF p. 6, Corollary 3.4: IID randomness dilution

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P42

open scoped BigOperators ComplexConjugate ENNReal

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P07

open QAlgorithms.Papers.Independent.Gap48.P20

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability shannon)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF pp.6--7, Corollary 3.4: IID randomness dilution. kappa is absolute,
c depends only on q, and the threshold does not depend on M. -/
theorem iidRandomnessDilution :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (Y : Type) [Fintype Y] [Nonempty Y] (q : Y → ℝ), IsProbability q →
        ∃ c : ℝ, 0 < c ∧ ∀ eps > (0 : ℝ), ∀ delta > (0 : ℝ), ∃ N : ℕ,
          ∀ n ≥ N, 1 ≤ n → ∀ M : ℕ, 1 ≤ M →
            let gamma := (2 : ℝ) ^ ((n : ℝ) * (shannon q + c * delta))
            bookProbability q n M (fun book => 2 * eps ≤ dilutionError q n M book) ≤
              2 * gamma * Real.exp (-kappa * M * eps ^ 2 / gamma) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P42

end
