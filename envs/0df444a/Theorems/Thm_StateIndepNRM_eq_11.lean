-- Prove2me | Theorems.Thm_StateIndepNRM_eq_11
-- name    : StateIndepNRM.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:39:11.936624+00:00
-- url     : https://prove2.me/theorems/bd2ecc5b-8014-479a-89fd-23ec6643f09f
-- title:
--   (11), p.12 — integral bound on $\mathbb E[(T-\tau_n)^+]$
-- statement:
--   Let $\Lambda^*_n[t,\tilde t]=\int_t^{\tilde t}\lambda^*_{n,v}\,dv$, let $\underline\lambda_n>0$ be a lower bound on $\lambda^*_{n,t}$ on $[0,T]$, and let $T'\in[0,T]$ satisfy $\Lambda^*_n[0,T']=D_n=\lfloor\Lambda^*_n[0,T]\rfloor$. Then
--
--   $$
--   \mathbb E[(T-\tau_n)^+]\le\int_0^{T'}e^{-\frac{(\Lambda^*_n[t,T'])^2}{2\Lambda^*_n[0,T']}}\,dt+\frac1{\underline\lambda_n}.
--   $$
--
--   This is the step where the Poisson tail bound (12) enters the proof of Lemma 1.
--
--   **Formalization Note** If $D_n=0$ then $T'=0$ and the integral is over an empty range, so Lean's $x/0=0$ inside it is never read.
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
--   - generalization: λ̲_n the minimum of the optimal rate of product n (p.10) → lo n any positive lower bound on [0,T]; no upper bound on the rates; reason: the page's constant is one such bound, and λ̄_n is never used
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - generalization: λ* piecewise constant (p.10) → l any measurable optimal solution; reason: the page's piecewise-constant solution is one such l
--   - encoding: T′ defined by Λ*_n[0,T′] = D_n (p.12) → any T′ ∈ [0,T] with that property, as a hypothesis; reason: it exists by the intermediate value theorem and is unique, since the rate is bounded below
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (11), p.12 (T′: p.12)

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- (11), p.12 (SSRN 3831496):
`E[(T − τₙ)⁺] ≤ ∫₀^{T′} exp(−Λ*ₙ[t,T′]² / (2 Λ*ₙ[0,T′])) dt + 1/λ̲ₙ`, where `T′ ∈ [0, T]` satisfies
`Λ*ₙ[0, T′] = Dₙ`.

**Formalization Note.** `T′` is any point with the property of p.12 (there is exactly one, since the
rate is bounded below by `lo n > 0`). If `Dₙ = 0` then `T′ = 0` and the integral is over an empty
range, so Lean's `x / 0 = 0` inside it is never read. -/
theorem eq_11 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    (lo : Fin N → ℝ) (hlo : ∀ n, 0 < lo n)
    (hlol : ∀ n, ∀ t ∈ Icc 0 I.T, lo n ≤ l t n)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration (Icc (0 : ℝ) I.T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (hX : IsPoissonDemand I.T l 𝓕 X P)
    (n : Fin N) (T' : ℝ) (hT' : T' ∈ Icc 0 I.T)
    (hD : ∫ t in (0 : ℝ)..T', l t n = fluidStock I.T l n) :
    ∫ ω, max (I.T - productStockoutTime I.T l n X ω) 0 ∂P ≤
      (∫ t in (0 : ℝ)..T', Real.exp (-((∫ v in t..T', l v n) ^ 2 /
        (2 * ∫ v in (0 : ℝ)..T', l v n)))) + 1 / lo n := by sorry

end StateIndepNRM
