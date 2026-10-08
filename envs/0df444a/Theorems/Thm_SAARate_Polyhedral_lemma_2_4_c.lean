-- Prove2me | Theorems.Thm_SAARate_Polyhedral_lemma_2_4_c
-- name    : SAARate.Polyhedral.lemma_2_4_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:06.143985+00:00
-- url     : https://prove2.me/theorems/90038382-3b99-4807-9ea5-072827408605
-- title:
--   Lemma 2.4 (c), p. 6 — under (2.13), A_N is a nonempty face of A
-- statement:
--   Assume the conditions of Theorem 2.3: (i) $\Omega$ is finite; (ii) every $h(\cdot,\omega)$ is piecewise linear and convex; (iii) $\Theta$ is closed, convex and polyhedral; (iv) the set $A$ of optimal solutions of the true problem $\min_{x\in\Theta}f(x)$ is nonempty and bounded. Assume also that every scenario has positive probability.
--
--   Then there are $q\ge\ell$ and points $x_1,\dots,x_q\in\mathbb R^m$, chosen independently of the sample, such that
--
--   1. $x_1,\dots,x_\ell$ form the set of extreme points of $A$;
--   2. $f(x_i)<f(x_j)$ for every $i\in\{1,\dots,\ell\}$ and $j\in\{\ell+1,\dots,q\}$;
--   3. for every sample path and every $N$, if
--   $$
--   \hat f_N(x_i)<\hat f_N(x_j)\quad\text{for all } i\in\{1,\dots,\ell\},\ j\in\{\ell+1,\dots,q\},\tag{2.13}
--   $$
--   then the set $A_N$ of optimal solutions of $\min_{x\in\Theta}\hat f_N(x)$ is nonempty and forms a face of $A$.
--
--   The condition (2.13) involves only finitely many sample averages at fixed points, so the event that $A_N$ is a nonempty face of $A$ is controlled by finitely many one-dimensional deviations. This is the deterministic core of Theorems 2.3 and 3.2.
--
--   **Formalization Note** (a) Clause 2 is not in the printed statement of (c); the proof of Theorem 3.2 (p. 12) recalls it, and the second proof of Theorem 2.3 (p. 8) uses it. Without it the statement would be trivially satisfiable, by repeating an extreme point of $A$ among $x_{\ell+1},\dots,x_q$ so that (2.13) never holds. (b) The paper writes $\ell<q$; here $\ell\le q$. The paper's proof first reduces to $\Theta=\mathbb R^m$ by adding an exact penalty $\alpha\,\mathrm{dist}_1(x,\Theta)$, and its $f$ in clause 2 is the penalised function. For the unpenalised $f$ and $\Theta=A$ (for example $h\equiv0$, $\Theta=[0,1]$) no point $x_j$ satisfies clause 2, so $\ell<q$ cannot hold; when $\Theta\ne A$ the existence of an outer point is not lost. (c) Every scenario is assumed to have positive mass ($P\{\omega\}\ne0$; p. 3 takes $\Omega$ to be the support of $P$); the clause "for any realization" fails otherwise. (d) Indices are 0-based in Lean: $\{1,\dots,\ell\}$ is `i.val < ℓ` and $\{\ell+1,\dots,q\}$ is `ℓ ≤ j.val` in `Fin q`. "Extreme points" is Mathlib's `Set.extremePoints`, and clause 1 is an equality of sets.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 6, Lemma 2.4 (c), (2.13); p. 12, proof of Theorem 3.2 (f(x_i) < f(x_j)); p. 3, (2.1) for the finite support

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting

open MeasureTheory ProbabilityTheory

namespace SAARate.Polyhedral

/-- Lemma 2.4 (c), p. 6, with the gap `f(x_i) < f(x_j)` recalled on p. 12: under (i)–(iv)
there are finitely many points `x_1, …, x_q`, independent of the sample, whose first `ℓ` form
the set of extreme points of `A`, with `f(x_i) < f(x_j)` for `i ≤ ℓ < j`, and such that for
every sample path and every `N`, condition (2.13) forces `A_N` to be nonempty and a face of `A`.
Indices are 0-based: the paper's `{1, …, ℓ}` is `i.val < ℓ`, its `{ℓ+1, …, q}` is `ℓ ≤ j.val`.
`hP` (every scenario has positive mass, p. 3) is a disclosed pin; the paper's `ℓ < q` is
`ℓ ≤ q` here (see the Formalization Note). -/
theorem lemma_2_4_c {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : ∀ ω, P {ω} ≠ 0)
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (hΘp : IsPolyhedral Θ)
    (hA : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ)) :
    ∃ (q ℓ : ℕ), ℓ ≤ q ∧ ∃ x : Fin q → SAARate.Sharp.E m,
      {y | ∃ i : Fin q, i.val < ℓ ∧ x i = y} =
          Set.extremePoints ℝ (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) ∧
        (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val →
          SAARate.Sharp.expectedObj P h (x i) < SAARate.Sharp.expectedObj P h (x j)) ∧
        ∀ (s : ℕ → Ω) (N : ℕ),
          (∀ i j : Fin q, i.val < ℓ → ℓ ≤ j.val → SAARate.Sharp.saaObj h s N (x i) < SAARate.Sharp.saaObj h s N (x j)) →
            (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ).Nonempty ∧
              IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h s N) Θ) := by sorry

end SAARate.Polyhedral
