-- Prove2me | Theorems.Thm_TalagrandCore_poisson_upper_tail
-- name    : TalagrandCore.poisson_upper_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:30.956662+00:00
-- url     : https://prove2.me/theorems/41cbfa52-4fb8-43a3-b2d6-75d16cd91f77
-- title:
--   Poissonian upper tail for a finite Bernoulli linear supremum
-- statement:
--   Let $Z$ be a finite centered Bernoulli linear supremum with coefficient envelope one. Put $w=\sigma^2+\mathbb E\Sigma^2+\mathbb E\bar Z>0$. For every $u\ge0$,
--
--   $$
--   \mathbb P\{Z\ge\mathbb EZ+u\}
--   \le 3\exp\!\left(-\frac{u}{3200}\log\left(1+\frac{u}{w}\right)\right).
--   $$
--
--   This is the full upper-tail estimate obtained by combining the Gaussian regime with Ledoux’s truncation argument.
--
--   **Formalization Note** The numerical constant is the explicit constant in the accepted finite-Boolean proof.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem poisson_upper_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {u : ℝ} (hu : 0 ≤ u)
    (hw4 : 0 < sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
      Ex (p : ℝ) (Zbar coeff (p : ℝ))) :
    Ex (p : ℝ) (fun ω => if Ex (p : ℝ) (Zproc coeff (p : ℝ)) + u ≤
        Zproc coeff (p : ℝ) ω then (1:ℝ) else 0) ≤
      3 * Real.exp (-((u / 3200) *
        Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Sigma2 coeff (p : ℝ)) +
          Ex (p : ℝ) (Zbar coeff (p : ℝ)))))) := by sorry

end TalagrandCore
