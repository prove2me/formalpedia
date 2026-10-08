-- Prove2me | Theorems.Thm_SatiaLave_Bayes_jensen_pointmass_priors
-- name    : SatiaLave.Bayes.jensen_pointmass_priors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:44:24.127667+00:00
-- url     : https://prove2.me/theorems/c6c69455-74dd-4a52-a0a3-24faa70b5bf3
-- title:
--   Proof of Proposition 9 — Jensen over point-mass priors: f(i, g) ≤ ∫ f(i, δ_P) dg(P)
-- statement:
--   Let $f(i,g)$ be a bounded solution of the Bayesian recursive equations (10) of Satia and Lave, $g$ a prior on the unknown transition matrix $P$, and $i$ a state. For a matrix $P$ let $\delta_P$ be the point mass at $P$. Then the function $P \mapsto f(i, \delta_P)$ is $g$-integrable and
--   $$
--   f(i, g) \le \int f(i, \delta_P)\, dg(P).
--   $$
--
--   In the paper this is the first line of the display in the proof of Proposition 9: with $a_x$ the point mass at $x$ and $y$ a random point mass distributed by $h(a_x) = g(x)$, so that $Ey = g$, Jensen's inequality for the convex function $f(i,\cdot)$ gives $f(i,g) = f(i, Ey) \le Ef(i,y) = \int f(i,y)\, dH(y)$. By the no-learning reduction, $f(i,\delta_P)$ is the optimal return of the process with known $P$, so the bound says that the Bayesian optimal return never exceeds the expected optimal return under full information.
--
--   **Formalization Note** Two departures, both forced by the argument. (1) Proposition 8 is convexity along finite mixtures, while this step is Jensen's inequality for the integral mixture $g = \int \delta_P\, dg(P)$; the statement asserts the integral form directly. (2) The paper restricts $x$ by "$x_i^k \in S_i^k$", but $Ey = g$ requires point masses at every transition-probability matrix, and the next line of the display splits the integral over $P \in S$ and $P \notin S$; the integral therefore ranges over the whole prior. Integrability is part of the conclusion, not an assumption.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, pp. 735-736, Proof of Proposition 9 (first line of the display on p. 736)

import Mathlib
import Definitions.Def_SatiaLave_Bayes_Model

open MeasureTheory

namespace SatiaLave.Bayes

/-- Proof of Proposition 9, p. 736 (first line of the display): writing a prior `g` as the
mixture `∫ δ_P dg(P)` of point masses, Jensen's inequality for the convex function `f(i, ·)`
gives `f(i, g) ≤ ∫ f(i, δ_P) dg(P)`. -/
theorem jensen_pointmass_priors {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D)
    (f : S → Measure (Mat S D) → ℝ) (hf : SolvesEq10 M f) (hb : IsBoundedOnPriors f)
    (g : Measure (Mat S D)) (hg : IsPrior g) (i : S) :
    Integrable (fun P => f i (Measure.dirac P)) g ∧
      f i g ≤ ∫ P, f i (Measure.dirac P) ∂g := by sorry

end SatiaLave.Bayes
