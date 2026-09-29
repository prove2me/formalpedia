-- Prove2me | Theorems.Thm_TalagrandCore_sigma2_expectation_bound
-- name    : TalagrandCore.sigma2_expectation_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:17.801513+00:00
-- url     : https://prove2.me/theorems/a20be97e-5834-4b79-8b73-bd84e6b791a4
-- title:
--   Expectation bound for the random variance process
-- statement:
--   For a finite centered Bernoulli linear class with coefficient envelope one and deterministic variance proxy $\sigma^2$, the random variance process satisfies
--
--   $$
--   \mathbb E\Sigma^2\le \sigma^2+8\,\mathbb E\bar Z.
--   $$
--
--   The proof combines symmetrization, Rademacher contraction, and desymmetrization. This estimate removes the random variance term from the final concentration bound.
--
--   **Formalization Note** $\bar Z$ is the maximum absolute centered linear sum over the finite class.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem sigma2_expectation_bound (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq) :
    Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) ≤
      sigmaSq + 8 * Ex (p : ℝ) (Zbar coeff (p : ℝ)) := by sorry

end TalagrandCore
