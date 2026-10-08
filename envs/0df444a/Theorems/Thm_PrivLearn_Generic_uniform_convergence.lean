-- Prove2me | Theorems.Thm_PrivLearn_Generic_uniform_convergence
-- name    : PrivLearn.Generic.uniform_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:58.863986+00:00
-- url     : https://prove2.me/theorems/c8e1f2ab-e28c-4852-a023-ae1734d05abb
-- title:
--   Proof of Theorem 3.4, p. 11 — uniform convergence of the training error over $\mathcal H_d$
-- statement:
--   Let $X$ be a finite set of examples, $P$ a probability distribution on $X\times\{0,1\}$, $H$ a finite class of hypotheses $X\to\{0,1\}$ and $\rho>0$. Draw a database $z$ of $n$ labeled examples i.i.d. from $P$. Then
--
--   $$\Pr_{z\sim P^n}\big[\,|\mathrm{err}(h)-\mathrm{err}_T(h)|\ge\rho\ \text{for some } h\in H\big]\le 2|H|\exp(-2n\rho^2).$$
--
--   Here $\mathrm{err}(h)$ is the error of $h$ on $P$ and $\mathrm{err}_T(h)$ its fraction of mistakes on $z$. This is the first step of the proof of Theorem 3.4: with high probability every hypothesis's training error is close to its true error.
--
--   **Formalization Note.** $P^n$ is the product measure on `Fin n → X × Bool`. For $n=0$ the training error is $0$ by Lean's convention and the right side is $2|H|$, so the statement is trivially true there.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 11, proof of Theorem 3.4, displays after 'By Chernoff-Hoeffding bounds'

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivLearn_Generic_ExpMech

open MeasureTheory

namespace PrivLearn.Generic

/-- Proof of Theorem 3.4 (p. 11): for `n` i.i.d. examples from `P` and every `ρ > 0`,
`Pr[|err(h) − err_T(h)| ≥ ρ for some h ∈ H] ≤ 2|H| exp(−2nρ²)`. -/
theorem uniform_convergence {X : Type*} [Fintype X] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (H : Finset (X → Bool)) (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (Measure.pi fun _ : Fin n => P) {z | ∃ h ∈ H, ρ ≤ |err P h - errT z h|}
      ≤ ENNReal.ofReal (2 * H.card * Real.exp (-2 * n * ρ ^ 2)) := by sorry

end PrivLearn.Generic
