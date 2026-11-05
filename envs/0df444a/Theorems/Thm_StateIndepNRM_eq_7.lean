-- Prove2me | Theorems.Thm_StateIndepNRM_eq_7
-- name    : StateIndepNRM.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:00.47709+00:00
-- url     : https://prove2.me/theorems/35db4c57-fc86-4b37-a2f3-95341141cb29
-- title:
--   (7), p.11 — $\Delta=\mathbb E[\Pi'(\tau,T]]\le\bar r^*\,\mathbb E[(T-\tau)^+]$
-- statement:
--   In the setting of (3), let $\bar r^*>0$ bound the optimal revenue rate: $r^*_t\le\bar r^*$ on $[0,T]$. Then
--
--   $$
--   \Delta=\mathbb E[\Pi'(\tau,T]]\le\bar r^*\cdot\mathbb E[(T-\tau)^+],
--   $$
--
--   where $\Pi'(\tau,T]$ is the revenue of the relaxed policy after $\tau$, whose expectation is $\mathbb E\int_\tau^Tr^*_t\,dt$.
--
--   This turns the gap into the expected time lost to the first stock-out.
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
--   - encoding: E[Π′(τ,T]], the relaxed policy's revenue after τ → E∫_τ^T r*_t dt; reason: the relaxed policy keeps the rate λ* throughout, so this is its revenue-rate form
--   - generalization: r̄* the bound of (2) on the optimal revenue rate → rBar any positive bound; reason: the page's constant is one such bound
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - generalization: λ* piecewise constant, with rates in [λ̲_n, λ̄_n] (p.10) → l any measurable optimal solution, with no bound on the rates; reason: the page's piecewise-constant solution is one such l, and this step does not use the rate bounds
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (7), p.11

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- (7), p.11 (SSRN 3831496): `Δ = E[Π′(τ, T]] ≤ r̄* · E[(T − τ)⁺]`.

**Formalization Note.** `E[Π′(τ, T]]` is the relaxed policy's expected revenue after `τ`, which is
`E ∫_τ^T r*_t dt`: the relaxed policy keeps the rate `l` throughout. -/
theorem eq_7 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    (rBar : ℝ) (hrBar : 0 < rBar)
    (hrl : ∀ t ∈ Icc 0 I.T, I.revRate t (l t) ≤ rBar)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (hX : IsPoissonDemand I.T l 𝓕 X P) :
    mtsDelta I l P X = ∫ ω, (∫ t in stockoutTime I.T l X ω..I.T, I.revRate t (l t)) ∂P ∧
    ∫ ω, (∫ t in stockoutTime I.T l X ω..I.T, I.revRate t (l t)) ∂P ≤
      rBar * ∫ ω, max (I.T - stockoutTime I.T l X ω) 0 ∂P := by sorry

end StateIndepNRM
