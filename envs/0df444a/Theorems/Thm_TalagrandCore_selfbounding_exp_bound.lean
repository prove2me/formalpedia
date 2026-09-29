-- Prove2me | Theorems.Thm_TalagrandCore_selfbounding_exp_bound
-- name    : TalagrandCore.selfbounding_exp_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:58:44.106193+00:00
-- url     : https://prove2.me/theorems/de54d480-1d74-4587-8fd0-d3a7284e6127
-- title:
--   Self-bounding exponential moment inequality for finite supremum processes
-- statement:
--   Consider a finite supremum process $Y=\max_a\sum_x g_a(x,\omega_x)$ whose coordinate summands lie in $[0,1]$. For every $\lambda\ge0$,
--
--   $$
--   \mathbb E e^{\lambda Y}\le
--   \exp\!\left((e^\lambda-1)\mathbb E Y\right).
--   $$
--
--   This is the Laplace-transform form of the self-bounding inequality used in Ledoux’s upper-tail argument.
--
--   **Formalization Note** The process is indexed by finite types and evaluated under the product Bernoulli expectation `Ex`.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem selfbounding_exp_bound (p : NNReal) (hp : p ≤ 1)
    (g : ι → κ → Bool → ℝ) (hg0 : ∀ a x b, 0 ≤ g a x b) (hg1 : ∀ a x b, g a x b ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    Ex (p : ℝ) (fun ω => Real.exp (lam * supProc g ω)) ≤
      Real.exp (Ex (p : ℝ) (fun ω => supProc g ω) * (Real.exp lam - 1)) := by sorry

end TalagrandCore
