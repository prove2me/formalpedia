-- Prove2me | Theorems.Thm_TalagrandCore_two_sided_tail
-- name    : TalagrandCore.two_sided_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:54.546267+00:00
-- url     : https://prove2.me/theorems/e6fc8b27-6104-4bfc-85fe-2ae006e8624d
-- title:
--   Two-sided Talagrand log-tail bound with unit envelope
-- statement:
--   Let $Z$ be a finite centered Bernoulli linear supremum with coefficient envelope one, variance proxy $\sigma^2$, and absolute supremum $\bar Z$. If $\sigma^2+\mathbb E\bar Z>0$, then for every $u\ge0$,
--
--   $$
--   \mathbb P\{|Z-\mathbb EZ|>u\}
--   \le 3\exp\!\left(-\frac{u}{57600}\log\left(1+\frac{u}{\sigma^2+\mathbb E\bar Z}\right)\right).
--   $$
--
--   This is the unit-envelope assembly of the Ledoux upper tail, the variance-process expectation estimate, and the Klein–Rio lower tail.
--
--   **Formalization Note** The event probability is represented by the expectation of its Boolean indicator.
-- source:
--   Emmanuel Candès and Justin Romberg, Sparsity and Incoherence in Compressive Sampling, Section 3, Theorem 3.2 and equation (3.9), PDF p. 12. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem two_sided_tail (p : NNReal) (hp : p ≤ 1) (coeff : ι → κ → ℝ)
    (hB : ∀ a x, |coeff a x| ≤ 1) {sigmaSq : ℝ} (hs : 0 ≤ sigmaSq)
    (hVar : ∀ a, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    {u : ℝ} (hu : 0 ≤ u)
    (hw : 0 < sigmaSq + Ex (p : ℝ) (Zbar coeff (p : ℝ))) :
    Ex (p : ℝ) (fun ω => if ¬ |Zproc coeff (p : ℝ) ω -
        Ex (p : ℝ) (Zproc coeff (p : ℝ))| ≤ u then (1:ℝ) else 0) ≤
      3 * Real.exp (-((u / 57600) *
        Real.log (1 + u / (sigmaSq + Ex (p : ℝ) (Zbar coeff (p : ℝ)))))) := by sorry

end TalagrandCore
