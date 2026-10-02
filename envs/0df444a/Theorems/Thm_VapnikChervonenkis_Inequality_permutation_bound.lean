-- Prove2me | Theorems.Thm_VapnikChervonenkis_Inequality_permutation_bound
-- name    : VapnikChervonenkis.Inequality.permutation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:18:18.978977+00:00
-- url     : https://prove2.me/theorems/cde1ec04-0657-40ec-8f39-134fc9ed4399
-- title:
--   Per-sample permutation bound — $\frac{1}{(2l)!}\sum_i \theta(\rho^{(l)}(T_iX_{2l}) - \varepsilon/2) \le 2\Delta^S(x_1,\dots,x_{2l})e^{-\varepsilon^2 l/8}$
-- statement:
--   Let $S$ be a collection of subsets of a set $X$, let $l \ge 1$, $\varepsilon > 0$, and fix a double sample $X_{2l} = (x_1, \dots, x_{2l})$. For each of the $(2l)!$ permutations $T_i$ of the $2l$ positions, compute the semi-sample deviation $\rho^{(l)}(T_i X_{2l})$ of the rearranged sample. With $\theta(z) = 1$ for $z \ge 0$ and $0$ for $z < 0$,
--   $$
--   \frac{1}{(2l)!} \sum_{i=1}^{(2l)!} \theta\Bigl(\rho^{(l)}(T_i X_{2l}) - \frac{\varepsilon}{2}\Bigr) \le 2\, \Delta^S(x_1, \dots, x_{2l})\, e^{-\varepsilon^2 l / 8},
--   $$
--   where $\Delta^S(x_1, \dots, x_{2l})$ is the index of $S$ on the sample. Since the index is at most the growth function, the right side is at most $2\, m^S(2l)\, e^{-\varepsilon^2 l/8}$.
--
--   The bound is deterministic: no probability measure enters. It is the estimate of the integrand of Eq. (11), and only the finitely many different subsamples that $S$ induces on the fixed sample matter.
--
--   **Formalization Note** $T_i X_{2l}$ is `x ∘ σ` for `σ : Equiv.Perm (Fin (l + l))`, and the average of the indicators is the number of such $\sigma$ with $\rho^{(l)}(x \circ \sigma) \ge \varepsilon/2$ divided by $(2l)!$. The statement is the index form of the paper's display, which implies the growth-function form. The paper's text before the display (pp. 270–271) describes the bracketed average as counting arrangements "for which $|\nu'_A - \nu''_A| \le \tfrac12\varepsilon$"; the indicator $\theta(\rho_A - \varepsilon/2)$ and the index set of $\Gamma$ count those with $\ge \tfrac12\varepsilon$, which is what is stated here.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 271, display after 'Thus,' (proof of Theorem 2)

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Inequality

/-- **The per-sample permutation bound** (p. 271, display after "Thus,"): for every fixed
double sample `x = (x_1, …, x_{2l})`, the fraction of the `(2l)!` permutations `σ` for which
the permuted sample `x ∘ σ` has `ρ^(l) ≥ ε/2` is at most `2 Δ^S(x_1, …, x_{2l}) e^{−ε² l / 8}`
(and hence at most `2 m^S(2l) e^{−ε² l / 8}`). No measure is involved. -/
theorem permutation_bound {X : Type*} (S : Set (Set X)) (ε : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hε : 0 < ε) (x : Fin (l + l) → X) :
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (l + l)) =>
        ε / 2 ≤ Shared.semiSampleDeviation S l (x ∘ σ))).card : ℝ) / ((l + l).factorial : ℝ)
      ≤ 2 * (Shared.index S x : ℝ) * Real.exp (-(ε ^ 2 * l / 8)) := by sorry

end VapnikChervonenkis.Inequality
