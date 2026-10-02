-- Prove2me | Theorems.Thm_TeschlODE_Frobenius_first_order_frobenius
-- name    : TeschlODE.Frobenius.first_order_frobenius
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:17:48.565756+00:00
-- url     : https://prove2.me/theorems/01ae052c-7fa2-4344-8224-6519e3e0a285
-- title:
--   Lemma 4.4 — u' + p(z)u = 0 has a solution z^α h(z) iff p has at most a simple pole
-- statement:
--   Let $R \in (0, \infty]$ and let $p$ be holomorphic in the punctured disc $0 < |z| < R$. Then:
--
--   1. The first-order equation
--   $$u'(z) + p(z)\,u(z) = 0 \qquad (4.28)$$
--   has a solution of the form
--   $$u(z) = z^\alpha h(z), \qquad h(z) = \sum_{j=0}^\infty h_j z^j, \quad h_0 = 1, \qquad (4.29)$$
--   if and only if $p$ has at most a first-order pole at $0$.
--   2. In this case $\alpha = -\lim_{z \to 0} z\,p(z)$, and the radius of convergence of the power series of $h$ is at least $R$, i.e. at least the radius of convergence of the Laurent series of $p$.
--
--   The lemma is the one-dimensional model of Fuchs's theorem, and it is used in the proof of Theorem 4.5 to produce the logarithmic second solution.
--
--   **Formalization Note.** "A solution of the form (4.29)": some $\alpha \in \mathbb{C}$ and some $h$ analytic at $0$ with $h(0) = 1$ such that $u(z) = z^\alpha h(z)$ satisfies $u'(z) = -p(z)u(z)$ at every point of a slit punctured disc $\{0 < |z| < \rho\} \setminus (-\infty, 0]$, $\rho > 0$, with the principal branch of $z^\alpha$ (`slitDisc ρ`). "At most a first-order pole" is `HasPoleOfOrderAtMost p 1`. The limit is taken over $z \to 0$, $z \neq 0$. The radius claim is stated for every such solution: every formal power series of $h$ at $0$ has radius $\ge R$. **Correction of the book (trap 30):** the book says the two radii "are the same"; only "at least" holds. For $h(z) = 1 - z$, $\alpha = 0$, $p(z) = 1/(1-z)$ the power series of $h$ has infinite radius while that of $p$ has radius $1$. The statement proves the true inequality, which is the one Theorem 4.5 needs.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 117, Lemma 4.4

import Mathlib
import Definitions.Def_TeschlODE_Frobenius_slitDisc
import Definitions.Def_TeschlODE_Frobenius_HasPoleOfOrderAtMost

open Filter Topology

namespace TeschlODE.Frobenius

/-- Teschl, Lemma 4.4 (p. 117), with `p` analytic in the punctured disc `0 < |z| < R`.
(1) The equation `u' + p(z) u = 0` (4.28) has a solution `u(z) = z^α h(z)` with `h` analytic at
`0`, `h(0) = 1` (4.29) — on some slit punctured disc, principal branch of `z^α` — if and only if
`p` has at most a first-order pole at `0`.
(2) In this case `α = −lim_{z→0} z p(z)`, and the power series of `h` at `0` has radius of
convergence at least `R`, i.e. at least that of the Laurent series of `p`. The book says the two
radii "are the same"; only `≥` holds (`h(z) = 1 − z`, `p(z) = 1/(1 − z)`, `α = 0` is a
counterexample to equality), so the statement is the corrected `≥`. -/
theorem first_order_frobenius (p : ℂ → ℂ) (R : ENNReal) (hR : 0 < R)
    (hp : DifferentiableOn ℂ p (Metric.eball (0 : ℂ) R \ {0})) :
    ((∃ α : ℂ, ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 1 ∧ ∃ ρ : ENNReal, 0 < ρ ∧
        ∀ z ∈ slitDisc ρ, HasDerivAt (fun ζ => ζ ^ α * h ζ) (-(p z * (z ^ α * h z))) z) ↔
      HasPoleOfOrderAtMost p 1) ∧
    ∀ (α : ℂ) (h : ℂ → ℂ) (ρ : ENNReal), AnalyticAt ℂ h 0 → h 0 = 1 → 0 < ρ →
      (∀ z ∈ slitDisc ρ, HasDerivAt (fun ζ => ζ ^ α * h ζ) (-(p z * (z ^ α * h z))) z) →
      Tendsto (fun z => z * p z) (𝓝[≠] 0) (𝓝 (-α)) ∧
      ∀ ph : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt h ph 0 → R ≤ ph.radius := by sorry

end TeschlODE.Frobenius
