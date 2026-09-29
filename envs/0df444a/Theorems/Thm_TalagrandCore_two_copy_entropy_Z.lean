-- Prove2me | Theorems.Thm_TalagrandCore_two_copy_entropy_Z
-- name    : TalagrandCore.two_copy_entropy_Z
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:58:56.412083+00:00
-- url     : https://prove2.me/theorems/3a57ff90-5485-4e58-9679-4188f5f7a241
-- title:
--   Two-copy entropy inequality for a finite linear supremum process
-- statement:
--   For a centered finite Bernoulli linear supremum $Z$ with coefficient envelope one and variance proxy $\sigma^2$, define the random variance process $\Sigma^2$. For every $\lambda\ge0$,
--
--   $$
--   \lambda\mathbb E[Ze^{\lambda Z}]-\mathbb E[e^{\lambda Z}]\log\mathbb E[e^{\lambda Z}]
--   \le \lambda^2e^{2\lambda}\mathbb E\!\left[e^{\lambda Z}(\Sigma^2+\sigma^2)\right].
--   $$
--
--   This is the two-copy entropy estimate feeding the Gaussian upper-tail differential inequality.
--
--   **Formalization Note** Suprema are finite maxima, so measurable-selection issues are replaced by a finite argmax construction inside the proof.
-- source:
--   Michel Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), Theorems 2.4–2.5, pp. 63–87. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem two_copy_entropy_Z (p : NNReal) (hp : p ≤ 1)
    (coeff : ι → κ → ℝ) (hB : ∀ a x, |coeff a x| ≤ 1)
    (sigmaSq : ℝ)
    (hVar : ∀ a : ι, ∑ x : κ, (p : ℝ) * (1 - (p : ℝ)) * coeff a x ^ 2 ≤ sigmaSq)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    lam * Ex (p : ℝ) (fun ω => Zproc coeff (p : ℝ) ω *
        Real.exp (lam * Zproc coeff (p : ℝ) ω)) -
      Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω)) *
        Real.log (Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω))) ≤
      lam ^ 2 * Real.exp (2 * lam) *
        Ex (p : ℝ) (fun ω => Real.exp (lam * Zproc coeff (p : ℝ) ω) *
          (Sigma2 coeff (p : ℝ) ω + sigmaSq)) := by sorry

end TalagrandCore
