-- Prove2me | Theorems.Thm_StochApproxDyn_Interpolation_shadowing_estimate
-- name    : StochApproxDyn.Interpolation.shadowing_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:10:04.521953+00:00
-- url     : https://prove2.me/theorems/c6cc1787-c09a-402e-8925-397db9e29905
-- title:
--   Proposition 4.1, estimate (11) — under A2′ the shadowing error is at most C(T)[Δ(t − 1, T + 1) + sup γ̄]
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R^d$ be continuous and globally integrable, with induced flow $\Phi$. Fix $T>0$ and constants $L\ge0$, $K$. There is a constant $C=C(T)$, depending only on $T$, $F$, $L$ and $K$, with the following property. Whenever
--
--   1. the step sizes satisfy $\gamma_n\ge0$, $\sum_n\gamma_n=\infty$, $\gamma_n\to0$,
--   2. $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$ for all $n$,
--   3. assumption A1 holds, and
--   4. (A2′) for some $r>0$, $F$ is $L$-Lipschitz and bounded by $K$ on the $r$-neighbourhood of $\{x_n:n\ge0\}$,
--
--   then for all $t\ge0$ large enough
--   $$\sup_{0\le h\le T}\big\|X(t+h)-\Phi_h(X(t))\big\|\le C\Big[\Delta(t-1,T+1)+\sup_{t\le s\le t+T}\bar\gamma(s)\Big].$$
--
--   The estimate quantifies the asymptotic pseudotrajectory property: the shadowing error over a window of length $T$ is controlled by the noise modulus $\Delta$ and the step sizes, which is what the rate results built on Proposition 4.1 use.
--
--   **Formalization Note** The constant is chosen after $T$, $L$, $K$ (and the fixed $F$) and before the sequences, the radius $r$ and the time; "for $t$ large enough" is an existential threshold $t_0\ge1$ that may depend on the run. A1 is kept as a hypothesis: it is a standing assumption of Proposition 4.1, and the "Furthermore" clause adds A2′ to it. The neighbourhood in A2′ is read as a uniform $r$-neighbourhood (see the goal theorem).
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), pp. 12–13, Proposition 4.1, estimate (11) ("Furthermore, under assumption A2′ …")

import Mathlib
import Definitions.Def_StochApproxDyn_Interpolation_VectorFieldFlow
import Definitions.Def_StochApproxDyn_Interpolation_Scheme

open scoped NNReal Topology
open Filter

namespace StochApproxDyn.Interpolation

/-- Benaïm 1999, Proposition 4.1, estimate (11), p. 13. Let `F` be continuous and globally
integrable with flow `Φ`. For every `T > 0` and all constants `L ≥ 0`, `K` there is `C` (depending
only on `F`, `T`, `L`, `K`) such that: whenever the standing assumptions on `γ`, the recursion (7)
and A1 hold, and `F` is `L`-Lipschitz and bounded by `K` on the `r`-neighbourhood of
`{x_n : n ≥ 0}` for some `r > 0` (A2′), then for all `t` large enough (with `t ≥ 1`)
`sup_{0≤h≤T} ‖X(t + h) − Φ_h(X(t))‖ ≤ C [Δ(t − 1, T + 1) + sup_{t≤s≤t+T} γ̄(s)]`. -/
theorem shadowing_estimate {d : ℕ}
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (hint : IsGloballyIntegrable F)
    (Φ : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hΦ : IsFlowOf F Φ) :
    ∀ T : ℝ, 0 < T → ∀ L : ℝ≥0, ∀ K : ℝ, ∃ C : ℝ,
      ∀ (γ : ℕ → ℝ) (x U : ℕ → EuclideanSpace ℝ (Fin d)) (r : ℝ),
        IsStepSizeSeq γ → SatisfiesScheme F γ x U → SatisfiesA1 γ U → 0 < r →
        LipschitzOnWith L F (Metric.thickening r (Set.range x)) →
        (∀ y ∈ Metric.thickening r (Set.range x), ‖F y‖ ≤ K) →
        ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ h ∈ Set.Icc (0 : ℝ) T,
          ‖interpAffine γ x (t + h) - Φ h (interpAffine γ x t)‖ ≤
            C * (Delta γ U (t - 1) (T + 1) + sSup (stepInterp γ '' Set.Icc t (t + T))) := by sorry

end StochApproxDyn.Interpolation
