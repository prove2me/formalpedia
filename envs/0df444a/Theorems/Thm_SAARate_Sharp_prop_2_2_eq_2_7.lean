-- Prove2me | Theorems.Thm_SAARate_Sharp_prop_2_2_eq_2_7
-- name    : SAARate.Sharp.prop_2_2_eq_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:13.931986+00:00
-- url     : https://prove2.me/theorems/613f1f6c-0fcb-4a78-af2e-b0f577fcbefd
-- title:
--   Proposition 2.2, (2.7), p. 5 — lim_N ℋ(∂f̂_N(x), ∂f(x)) = 0 w.p.1
-- statement:
--   Let $P$ be a probability measure on $(\Omega,\mathcal F)$ and $h:\mathbb R^m\times\Omega\to\mathbb R$ with
--
--   1. $h(\cdot,\omega)$ convex for every $\omega\in\Omega$;
--   2. $f(x)=\mathbb E_P h(x,\omega)$ well defined and finite valued.
--
--   Let $\omega^1,\omega^2,\dots$ be an i.i.d. sample from $P$ and $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$. Write $\partial g(x)=\{v : g(y)-g(x)\ge\langle v,y-x\rangle\ \forall y\in\mathbb R^m\}$ for the subdifferential of a convex function and
--   $$
--   \mathcal H(B,C)=\max\Bigl\{\sup_{x\in C}\operatorname{dist}(x,B),\ \sup_{x\in B}\operatorname{dist}(x,C)\Bigr\} \tag{2.4}
--   $$
--   for the Hausdorff distance between sets $B,C\subset\mathbb R^m$. Then for every $x\in\mathbb R^m$,
--   $$
--   \lim_{N\to\infty}\mathcal H\bigl(\partial\hat f_N(x),\partial f(x)\bigr)=0\qquad\text{w.p.1}. \tag{2.7}
--   $$
--
--   The subdifferentials of the sample average function converge to that of the expected value function; this is the pointwise form of the uniform convergence used for piecewise linear problems (Lemma 2.4 (b)).
--
--   **Formalization Note.** The subdifferential is the published definition `ShorNonsmooth.Subdiff.subdifferential` with domain $\mathbb R^m$. The Hausdorff distance is Mathlib's extended-valued `Metric.hausdorffEDist` (in $[0,\infty]$), which agrees with (2.4) and has no junk value on empty or unbounded sets. The point $x$ is fixed before the almost-sure quantifier, as on the page.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 5, Proposition 2.2, (2.4), (2.7)

import Mathlib
import Definitions.Def_SAARate_Sharp_Setting
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

theorem prop_2_2_eq_2_7 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : IsIIDSample Q P ω) :
    ∀ x : E m, ∀ᵐ s ∂Q,
      Tendsto (fun N : ℕ => Metric.hausdorffEDist
          (ShorNonsmooth.Subdiff.subdifferential Set.univ (saaObj h (fun j => ω j s) N) x)
          (ShorNonsmooth.Subdiff.subdifferential Set.univ (expectedObj P h) x))
        atTop (𝓝 0) := by sorry

end SAARate.Sharp
