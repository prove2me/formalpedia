-- Prove2me | Theorems.Thm_RandOrderSort_proposition_4_15
-- name    : RandOrderSort.proposition_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:51.885167+00:00
-- url     : https://prove2.me/theorems/815a637c-f452-4bb7-a825-820328163fba
-- title:
--   Proposition 4.15 — fixed-cut exponential moment
-- statement:
--   There are absolute constants $\theta>0$, $A_0\ge 1$ and $\gamma_0\ge 0$ such that EmpiricalSort satisfies
--   $$\mathbb E[e^{\theta C(q)}]\le A_0n^{\gamma_0}\qquad\text{for every deterministic }q\in(0,1)$$
--   on $n\ge 2$ independent uniform inputs in $[0,1]$, uniformly in $q$ and $n$.
--
--   Here $C(q)$ counts the adjacent output pairs on opposite sides of $q$. This is the uniform-input result that §4.6 transfers to arbitrary fixed inputs.
--
--   Differences from the source:
--   - encoding: n independent uniform inputs, with keys almost surely distinct → the stream is the input order (π = σ = 1), with value ties broken by index, and integrability is stated; reason: ties have probability zero
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Proposition 4.15, p.37, display (55)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_iidUnif
open MeasureTheory

namespace RandOrderSort

/-- **Proposition 4.15 (Fixed-cut exponential moment)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.37: "There are absolute constants
θ > 0, A_0 ≥ 1, and γ_0 ≥ 0 such that EmpiricalSort, as specified above, satisfies
E[e^{θC(q)}] ≤ A_0 n^{γ_0} for every deterministic q ∈ (0, 1) (55) on n ≥ 2 independent uniform inputs in
[0, 1], uniformly in q, n."

**Formalization Note.** The constants are chosen before `n` and `q`. The inputs `X` have law
`iidUnif n` and arrive in index order (value ties, a null event, broken by index); `C(q)` is the
crossing count of EmpiricalSort's output at the threshold `q`. The integrand is integrable. -/
theorem proposition_4_15 :
    ∃ θ : ℝ, 0 < θ ∧ ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∃ γ₀ : ℝ, 0 ≤ γ₀ ∧ ∀ n, 2 ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      Integrable (fun X : Fin n → ℝ => Real.exp (θ * valueCrossings empiricalSort X 1 1 q)) (iidUnif n) ∧
      ∫ X, Real.exp (θ * valueCrossings empiricalSort X 1 1 q) ∂(iidUnif n) ≤
        A₀ * (n : ℝ) ^ γ₀ := by sorry

end RandOrderSort
