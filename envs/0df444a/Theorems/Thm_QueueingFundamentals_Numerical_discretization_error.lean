-- Prove2me | Theorems.Thm_QueueingFundamentals_Numerical_discretization_error
-- name    : QueueingFundamentals.Numerical.discretization_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T20:25:26.917189+00:00
-- url     : https://prove2.me/theorems/a12ab7c2-2a30-4e97-9fb0-f53dad5136d1
-- title:
--   Eqs. (8.27)–(8.28) — the discretization error of the Fourier-series inversion
-- statement:
--   Let $f$ be a real function on $[0,\infty)$ with Laplace transform $\bar f(s)=\int_0^\infty e^{-sx}f(x)\,dx$, and let $f_{A,n}(t)$ be the truncated Fourier-series approximant (8.25). Fix $A>0$ and $t>0$ and assume that $f$ is bounded and Lipschitz continuous on $[0,\infty)$. Then:
--
--   1. the approximants $f_{A,n}(t)$ converge as $n\to\infty$ to a limit $f_A(t)$ (the series (8.24));
--   2. (8.27) the discretization error is
--   $$f_A(t)-f(t)=\sum_{k=1}^{\infty}e^{-kA}f\big((2k+1)t\big);$$
--   3. (8.28) if $|f(x)|\le C$ for all $x>3t$, then
--   $$|f_A(t)-f(t)|\le \frac{C\,e^{-A}}{1-e^{-A}}.$$
--
--   The discretization error can therefore be made arbitrarily small by taking $A$ large, which is how the parameter $A$ of Algorithm 8.1 is chosen.
--
--   **Formalization Note** The book states (8.27) "provided that t is a continuity point of f(·)", quoting Abate et al. (1999) without proof. Continuity at $t$ alone does not make the series (8.24) converge, since the error formula comes from the Fourier series of a periodic function built from the values of $f$ at all odd multiples of $t$. This item therefore uses a stated strengthening of the hypotheses: $f$ bounded and Lipschitz on $[0,\infty)$. Boundedness also makes $\bar f(s)$ converge absolutely for $\mathrm{Re}\,s=A/(2t)>0$. The approximation "$\approx Ce^{-A}$" in (8.28) is not formalized.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.391, Eqs. (8.27)–(8.28) (with (8.24)–(8.25), p.390); hypotheses strengthened, see statement

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_FourierSeries

open Filter Topology

namespace QueueingFundamentals.Numerical

/-- Eqs. (8.27)–(8.28) (Gross et al., p.391), under a pinned hypothesis set. Let `A > 0`,
`t > 0`, and let `f` be bounded and Lipschitz on `[0, ∞)` (a strengthening of the book's
"t is a continuity point of f"). Then the approximants `f_{A,n}(t)` of (8.25) converge to a limit
`f_A(t)` (the series (8.24)), the discretization error is
`f_A(t) − f(t) = ∑_{k ≥ 1} e^{−kA} f((2k + 1)t)` (8.27), and if `|f(x)| ≤ C` for `x > 3t` then
`|f_A(t) − f(t)| ≤ C e^{−A}/(1 − e^{−A})` (8.28). -/
theorem discretization_error (f : ℝ → ℝ) (A t : ℝ) (hA : 0 < A) (ht : 0 < t)
    (K : NNReal) (hLip : LipschitzOnWith K f (Set.Ici 0))
    (M : ℝ) (hM : ∀ x : ℝ, 0 ≤ x → |f x| ≤ M) :
    ∃ fA : ℝ, Tendsto (fun n : ℕ => fourierApprox f A t n) atTop (𝓝 fA) ∧
      fA - f t = ∑' k : ℕ, Real.exp (-(((k : ℝ) + 1) * A)) * f ((2 * ((k : ℝ) + 1) + 1) * t) ∧
      ∀ C : ℝ, (∀ x : ℝ, 3 * t < x → |f x| ≤ C) →
        |fA - f t| ≤ C * (Real.exp (-A) / (1 - Real.exp (-A))) := by sorry

end QueueingFundamentals.Numerical
