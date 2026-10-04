-- Prove2me | Theorems.Thm_Soar_pool_law
-- name    : Soar.pool_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-22T18:59:45.508872+00:00
-- url     : https://prove2.me/theorems/b04880d2-eb18-4bf7-9eb2-e96c1e613234
-- title:
--   The permuted pool is i.i.d. and the true demand's slot is uniform
-- statement:
--   Let $\mathcal X$ be a measurable space and $P$ a probability measure on it. Fix $k \ge 0$ and consider the randomness of a SOAR epoch with $k + 1$ remaining supply units: the arriving demand unit $\hat x_0 \sim P$, the simulated units $\hat x_1, \dots, \hat x_k$ i.i.d. $P$, and a uniformly random permutation $\sigma \in S_{k+1}$, all independent. The permuted pool is the tuple $(\hat x_{\sigma(j)})_{j = 0, \dots, k} \in \mathcal X^{k+1}$, and the true arriving unit occupies slot $\sigma^{-1}(0)$. Then the joint law of the pair
--   $$\Bigl(\bigl(\hat x_{\sigma(j)}\bigr)_{j=0}^{k},\ \sigma^{-1}(0)\Bigr)$$
--   is the product $P^{\otimes (k+1)} \otimes \mathrm{Unif}\{0, \dots, k\}$: the pool the solver sees is an i.i.d. $P$ tuple, the slot of the true demand unit is uniform, and the two are independent.
--
--   **Role.** In the proof of Theorem 1 the paper conditions on the event $B$ that the pool is $\{x_0, \dots, x_{n-t}\}$ and the solver's output is $\eta$, and argues that the probability that $x_{\eta^{-1}(i)}$ is the true demand is $\frac{1}{n - t + 1}$ because the $n - t + 1$ pool units are i.i.d. and $\eta$ is independent of which unit is real. This statement isolates that independence: the solver's input is the pool alone, and the position of the real unit carries no information about it.
--
--   **Formalization Note** The statement is an identity of pushforward measures on $\mathcal X^{k+1} \times \{0, \dots, k\}$; the map is measurable because permutations carry the discrete $\sigma$-algebra. No quality function, supply, or solver enters. The case $k = 0$ says that a single unit with the trivial permutation has law $P \otimes \delta_0$.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 3.2.2, proof of Theorem 1 (the computation of $\mathbb P(A_i \mid B(x_0, \dots, x_{n-t}, \eta))$)

import Mathlib
import Definitions.Def_SoarPolicy

open MeasureTheory

namespace Soar

theorem pool_law {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (k : ℕ) :
    Measure.map (fun r : SoarEpochRand X k => (SoarPool r, r.2.2.symm 0))
        (SoarEpochMeasure P k)
      = (Measure.pi fun _ : Fin (k + 1) => P).prod (SoarUniform (Fin (k + 1))) := by
  sorry

end Soar
