-- Prove2me | Theorems.Thm_StateIndepNRM_theorem_1
-- name    : StateIndepNRM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:53.011577+00:00
-- url     : https://prove2.me/theorems/bee532a5-7523-4d54-aca0-85990e44e334
-- title:
--   Theorem 1, pp.10–11 — the MTS optimality gap is $O(\sqrt k)$ (corrected: $\Lambda^*_n[0,T]$ for $D_n$ in the $\sqrt k$ term)
-- statement:
--   Let $(\lambda^*_t)$ be an optimal solution of the deterministic problem of an instance, with $\Lambda^*_n[0,T]=\int_0^T\lambda^*_{n,t}\,dt$, $\underline\lambda_n>0$ a lower bound on $\lambda^*_{n,t}$ and $\bar r^*>0$ an upper bound on $r^*_t$ on $[0,T]$. For each integer $k\ge1$ let $X^{(k)}$ be a Poisson demand process with rate $k\lambda^*$. Then:
--
--   1. for every $k\ge1$, the MTS policy built on $X^{(k)}$ is admissible for $\mathbb P_{C,k}$;
--   2. for every $k\ge1$,
--
--   $$
--   \Pi_{C,k}-\Pi^{MTS}_{C,k}\le\Big(\bar r^*\sum_{n=1}^N\frac{\sqrt{\pi\,\Lambda^*_n[0,T]}}{\sqrt2\,\underline\lambda_n}\Big)\sqrt k+\sum_{n=1}^N\frac{\bar r^*}{\underline\lambda_n};
--   $$
--
--   3. $\Pi_{C,k}-\Pi^{MTS}_{C,k}=O(\sqrt k)$ as $k\to\infty$.
--
--   So a state-independent policy loses only a square-root amount against an optimal revenue of order $k$, even when the demand for a product depends on the prices of the other products.
--
--   **Formalization Note** $\underline\lambda_n$ and $\bar r^*$ are the unscaled constants. The demand processes are hypotheses: they exist, on the canonical space of counting paths, but the statement does not construct them.
--
--   Differences from the source:
--   - correction: D_n = ⌊Λ*_n[0,T]⌋ in the √k term (p.11) → Λ*_n[0,T] in the √k term; reason: the printed bound is false: with N = M = 1, a = b = T = 1, Λ = [0,1/2], R(λ) = 2λ − λ², one has λ* = 1/2, D = 0, r̄* = 3/4, λ̲ = 1/2, so the printed bound is 1.5 for every k, while the gap is at least 2.98 at k = 50; the proof's claim that D_n scales by k fails for a floor, and ⌊kΛ*_n⌋ ≤ kΛ*_n gives the corrected constant, equal to the printed one when Λ*_n[0,T] is an integer
--   - generalization: prices with an invertible rate–price map on each piece → rates are chosen directly; R_t is data and no price map is modelled; reason: the page states the two are equivalent (p.5), and any such map gives this data
--   - generalization: non-anticipatory pricing policies → progressively measurable rates in any filtration whose sales compensator is ∫λ, with unit-jump sales and capacity holding almost surely, randomization allowed; reason: this class contains the paper's policies, so the supremum is over at least as much and the bounds imply the paper's
--   - reading: a_{m,n} > 0, then a positive entry in every row and column (p.5) → 0 ≤ a m n with a positive entry in every row and column; reason: the row and column condition only has content for a_{m,n} ≥ 0; the case a_{m,n} > 0 is included
--   - encoding: Poisson rates and a null price vector (Assumption 2) → Λ j lies in the nonnegative orthant and R j 0 = 0; reason: rates are nonnegative, and a null price sells nothing so it earns nothing
--   - encoding: expected revenue with instantaneous expected revenue rate R_t(λ_t) (p.6) → E∫₀ᵀ R_t(λ_t) dt, with the revenue rate integrable on [0,T]×Ω; reason: the page's objective written as an integral; a policy without expected revenue has no objective value
--   - encoding: the probability space is not named → sample spaces range over Ω : Type; reason: a universe choice; canonical path spaces live in Type
--   - reading: two MTS policies: p.7 keeps selling the other products after τ, p.9 sets the null price vector → the §3 p.9 version: rate l up to τ, zero afterwards; reason: the page says its analysis uses this version (p.9)
--   - encoding: the time at which sales of some product equal D_n → the first time with D_n ≤ X n t; demand has every path a counting path; reason: the same time, since unit jumps hold almost surely; every-path regularity is a choice of version on the canonical space
--   - generalization: λ*_t piecewise constant, in [λ̲_n, λ̄_n], with λ̲_n and r̄* the exact extrema (p.10) → l any measurable optimal solution, lo and rBar any positive bounds, no upper bound on the rates; reason: the paper's piecewise-constant solution and its extrema are one choice; λ̄_n is never used
--   - generalization: Π_{C,k} − Π^MTS_{C,k} = O(√k) and the explicit bound → these two clauses, with admissibility of the MTS policy for every k ≥ 1 as a further clause; reason: the page takes it for granted, and it gives the gap's nonnegativity
--   - encoding: one sequence of scaled problems, each with its own demand process → one sample space carrying the filtration and the demand process of every k; reason: a product space carries any such family, and each clause reads one k at a time
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - generalization: the non-homogeneous multivariate Poisson process X with rate λ* (p.7) → any X with IsPoissonDemand, relative to any filtration whose past its increments are independent of, taken as a hypothesis; reason: the page's process with its natural filtration is one such pair, so the page's case is included
--   - encoding: k ∈ ℕ indexes the scaled problems (p.8) → k : ℕ with 1 ≤ k; reason: the page scales by a positive integer; at k = 0 there is no problem to speak of
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, Theorem 1, pp.10–11 (proof pp.11–13)

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- Theorem 1, pp.10–11 (Manchiraju–Dawande–Janakiraman, SSRN 3831496), with the corrected constant:
in the `k`-scaled problem `P_{C,k}`, the MTS policy is admissible, its optimality gap is at most
`(r̄* ∑ₙ √(π Λ*ₙ[0,T])/(√2 λ̲ₙ)) √k + ∑ₙ r̄*/λ̲ₙ`, and the gap is `O(√k)`.

**Formalization Note.** `lo` and `rBar` are the unscaled `λ̲ₙ`, `r̄*` of (2), for the optimal solution
`l` of the unscaled `P_Det`; `k • l` is the rate of `P_{C,k}`, so its stock is `⌊k Λ*ₙ[0,T]⌋`. The
page prints `Dₙ` in the `√k` term, which is false (`Dₙ` is a floor and does not scale by `k`), and
`Λ*ₙ[0,T]` is the minimal correction. A single `Ω` carries the demand processes of all `k`; each
clause reads one `k` at a time, so this loses nothing. The demand processes are hypotheses: they exist
(on the canonical space of counting paths), but the statement does not construct them. -/
theorem theorem_1 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l)
    (lo : Fin N → ℝ) (hlo : ∀ n, 0 < lo n)
    (hlol : ∀ n, ∀ t ∈ Icc 0 I.T, lo n ≤ l t n)
    (rBar : ℝ) (hrBar : 0 < rBar)
    (hrl : ∀ t ∈ Icc 0 I.T, I.revRate t (l t) ≤ rBar)
    {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : ℕ → Filtration (Icc (0 : ℝ) I.T) mΩ) (X : ℕ → Fin N → ℝ → Ω → ℕ)
    (hX : ∀ k, 1 ≤ k → IsPoissonDemand I.T (scaledRate k l) (𝓕 k) (X k) P) :
    (∀ k, 1 ≤ k → IsAdmissible (I.scale k) P (mtsPolicy I.T (scaledRate k l) (𝓕 k) (X k))) ∧
    (∀ k, 1 ≤ k →
      optimalRevenue (I.scale k) - mtsRevenue (I.scale k) (scaledRate k l) P (𝓕 k) (X k) ≤
        (rBar * ∑ n, Real.sqrt (Real.pi * ∫ t in (0 : ℝ)..I.T, l t n) / (Real.sqrt 2 * lo n)) *
          Real.sqrt k + ∑ n, rBar / lo n) ∧
    (fun k : ℕ =>
      optimalRevenue (I.scale k) - mtsRevenue (I.scale k) (scaledRate k l) P (𝓕 k) (X k))
      =O[Filter.atTop] (fun k : ℕ => Real.sqrt k) := by sorry

end StateIndepNRM
