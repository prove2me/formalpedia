-- Prove2me | Theorems.Thm_StateIndepNRM_eq_8
-- name    : StateIndepNRM.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:50.862196+00:00
-- url     : https://prove2.me/theorems/3f490eb4-a64d-4591-a1e6-84b58d6504ff
-- title:
--   (8), p.12 — $\mathbb E[(T-\tau)^+]\le\sum_n\mathbb E[(T-\tau_n)^+]$
-- statement:
--   With $\tau$ the stock-out time and $\tau_n$ the stock-out time of product $n$ under the demand process,
--
--   $$
--   \mathbb E[(T-\tau)^+]\le\sum_{n=1}^N\mathbb E[(T-\tau_n)^+].
--   $$
--
--   This separates the products, so each can be analysed through its own Poisson process.
--
--   Differences from the source:
--   - generalization: prices with an invertible rate–price map on each piece → rates are chosen directly; R_t is data and no price map is modelled; reason: the page states the two are equivalent (p.5), and any such map gives this data
--   - generalization: non-anticipatory pricing policies → progressively measurable rates in any filtration whose sales compensator is ∫λ, with unit-jump sales and capacity holding almost surely, randomization allowed; reason: this class contains the paper's policies, so the supremum is over at least as much and the bounds imply the paper's
--   - reading: a_{m,n} > 0, then a positive entry in every row and column (p.5) → 0 ≤ a m n with a positive entry in every row and column; reason: the row and column condition only has content for a_{m,n} ≥ 0; the case a_{m,n} > 0 is included
--   - encoding: Poisson rates and a null price vector (Assumption 2) → Λ j lies in the nonnegative orthant and R j 0 = 0; reason: rates are nonnegative, and a null price sells nothing so it earns nothing
--   - encoding: expected revenue with instantaneous expected revenue rate R_t(λ_t) (p.6) → E∫₀ᵀ R_t(λ_t) dt, with the revenue rate integrable on [0,T]×Ω; reason: the page's objective written as an integral; a policy without expected revenue has no objective value
--   - encoding: the probability space is not named → sample spaces range over Ω : Type; reason: a universe choice; canonical path spaces live in Type
--   - reading: two MTS policies: p.7 keeps selling the other products after τ, p.9 sets the null price vector → the §3 p.9 version: rate l up to τ, zero afterwards; reason: the page says its analysis uses this version (p.9)
--   - encoding: the time at which sales of some product (τ) or of product n (τ_n) equal D_n → the first time with D_n ≤ X n t; demand has every path a counting path; reason: the same time, since unit jumps hold almost surely; every-path regularity is a choice of version on the canonical space
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - generalization: the standing assumption of p.10: λ* piecewise constant, rates in [λ̲_n, λ̄_n], r*_t ≤ r̄* → not assumed; l is any measurable optimal solution; reason: this step does not use it, and the page's case is included
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (8), p.12 (τ_n: display, p.11)

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- (8), p.12 (SSRN 3831496): `E[(T − τ)⁺] ≤ ∑ₙ E[(T − τₙ)⁺]`. -/
theorem eq_8 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (hX : IsPoissonDemand I.T l 𝓕 X P) :
    ∫ ω, max (I.T - stockoutTime I.T l X ω) 0 ∂P ≤
      ∑ n, ∫ ω, max (I.T - productStockoutTime I.T l n X ω) 0 ∂P := by sorry

end StateIndepNRM
