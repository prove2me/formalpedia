-- Prove2me | Theorems.Thm_StateIndepNRM_eq_4
-- name    : StateIndepNRM.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:53.762174+00:00
-- url     : https://prove2.me/theorems/64544c81-c537-45a8-86f3-7d39ea1f04d1
-- title:
--   (3)–(4), p.11 — $\Pi_C-\Pi_C^{MTS}\le\Delta$
-- statement:
--   Let $(\lambda^*_t)$ be an optimal solution of $\mathbb P_{\mathrm{Det}}$, let $X$ be the Poisson demand process with rate $\lambda^*$, and let $\tau$ be its stock-out time. With
--
--   $$
--   \Delta:=\int_0^Tr^*_t\,dt-\mathbb E[\Pi[0,\tau]],
--   $$
--
--   where $\mathbb E[\Pi[0,\tau]]=\mathbb E\int_0^\tau r^*_t\,dt$, the optimality gap of the MTS policy satisfies
--
--   $$
--   \Pi_C-\Pi_C^{MTS}\le\Delta.
--   $$
--
--   This reduces the gap to the revenue that the fluid plan earns after the first stock-out.
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
--   - encoding: Π[0,τ] is the random revenue over [0,τ] → its expectation is written E∫₀^τ r*_t dt; reason: the revenue-rate form of the objective; the policy's rate is λ* on [0,τ]
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - generalization: the standing assumption of p.10: λ* piecewise constant, rates in [λ̲_n, λ̄_n], r*_t ≤ r̄* → not assumed; l is any measurable optimal solution; reason: this step does not use it, and the page's case is included
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (3)–(4), p.11

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- (3)–(4), p.11 (SSRN 3831496): `Δ` is an upper bound on the optimality gap of the MTS policy,
`Π_C − Π^MTS_C ≤ Δ`. -/
theorem eq_4 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (hX : IsPoissonDemand I.T l 𝓕 X P) :
    optimalRevenue I - mtsRevenue I l P 𝓕 X ≤ mtsDelta I l P X := by sorry

end StateIndepNRM
