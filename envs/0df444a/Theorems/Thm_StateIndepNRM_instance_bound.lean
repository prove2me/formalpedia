-- Prove2me | Theorems.Thm_StateIndepNRM_instance_bound
-- name    : StateIndepNRM.instance_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:00.770095+00:00
-- url     : https://prove2.me/theorems/435e012c-4535-45e8-a4bb-b9a879b2c6dd
-- title:
--   §3.1 display, p.13 — $\Pi_C-\Pi_C^{MTS}\le\bar r^*\sum_n(\sqrt{\pi D_n}/(\sqrt2\,\underline\lambda_n)+1/\underline\lambda_n)$
-- statement:
--   For one instance, with $D_n$ its own stock and the bounds $\underline\lambda_n$, $\bar r^*$ of (2),
--
--   $$
--   \Pi_C-\Pi_C^{MTS}\le\bar r^*\cdot\sum_{n=1}^N\Big(\frac{\sqrt{\pi D_n}}{\sqrt2\,\underline\lambda_n}+\frac1{\underline\lambda_n}\Big).
--   $$
--
--   This is the non-asymptotic bound; applied to the $k$-scaled instance it gives Theorem 1.
--
--   Differences from the source:
--   - generalization: prices with an invertible rate–price map on each piece → rates are chosen directly; R_t is data and no price map is modelled; reason: the page states the two are equivalent (p.5), and any such map gives this data
--   - generalization: non-anticipatory pricing policies → progressively measurable rates in any filtration whose sales compensator is ∫λ, with unit-jump sales and capacity holding almost surely, randomization allowed; reason: this class contains the paper's policies, so the supremum is over at least as much and the bounds imply the paper's
--   - reading: a_{m,n} > 0, then a positive entry in every row and column (p.5) → 0 ≤ a m n with a positive entry in every row and column; reason: the row and column condition only has content for a_{m,n} ≥ 0; the case a_{m,n} > 0 is included
--   - encoding: Poisson rates and a null price vector (Assumption 2) → Λ j lies in the nonnegative orthant and R j 0 = 0; reason: rates are nonnegative, and a null price sells nothing so it earns nothing
--   - encoding: expected revenue with instantaneous expected revenue rate R_t(λ_t) (p.6) → E∫₀ᵀ R_t(λ_t) dt, with the revenue rate integrable on [0,T]×Ω; reason: the page's objective written as an integral; a policy without expected revenue has no objective value
--   - encoding: the probability space is not named → sample spaces range over Ω : Type; reason: a universe choice; canonical path spaces live in Type
--   - reading: two MTS policies: p.7 keeps selling the other products after τ, p.9 sets the null price vector → the §3 p.9 version: rate l up to τ, zero afterwards; reason: the page says its analysis uses this version (p.9)
--   - encoding: the time at which sales of some product equal D_n → the first time with D_n ≤ X n t; demand has every path a counting path; reason: the same time, since unit jumps hold almost surely; every-path regularity is a choice of version on the canonical space
--   - generalization: r̄* and λ̲_n the constants of (2) (p.10), with λ̄_n an upper rate bound → rBar and lo n any positive bounds on [0,T]; no upper bound on the rates; reason: the page's constants are one choice, and λ̄_n is never used
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - generalization: λ* piecewise constant (p.10) → l any measurable optimal solution; reason: the page's piecewise-constant solution is one such l
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3.1 display, p.13

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- §3.1 display, p.13 (SSRN 3831496):
`Π_C − Π^MTS_C ≤ r̄* · ∑ₙ (√(πDₙ)/(√2 λ̲ₙ) + 1/λ̲ₙ)`, with `Dₙ` the instance's own stock. -/
theorem instance_bound {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    (lo : Fin N → ℝ) (hlo : ∀ n, 0 < lo n)
    (hlol : ∀ n, ∀ t ∈ Icc 0 I.T, lo n ≤ l t n)
    (rBar : ℝ) (hrBar : 0 < rBar)
    (hrl : ∀ t ∈ Icc 0 I.T, I.revRate t (l t) ≤ rBar)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (hX : IsPoissonDemand I.T l 𝓕 X P) :
    optimalRevenue I - mtsRevenue I l P 𝓕 X ≤
      rBar * ∑ n, (Real.sqrt (Real.pi * fluidStock I.T l n) / (Real.sqrt 2 * lo n) + 1 / lo n) := by sorry

end StateIndepNRM
