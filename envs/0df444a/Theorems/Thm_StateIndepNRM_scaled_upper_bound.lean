-- Prove2me | Theorems.Thm_StateIndepNRM_scaled_upper_bound
-- name    : StateIndepNRM.scaled_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:45.937167+00:00
-- url     : https://prove2.me/theorems/1d5a7802-7c90-4782-8cfc-8869f1456687
-- title:
--   §3 display, p.8 — $\Pi_{C,k}\le k\int_0^Tr^*_t\,dt$
-- statement:
--   Let $(\lambda^*_t)$ be an optimal solution of $\mathbb P_{\mathrm{Det}}$ for the unscaled instance, with $r^*_t=R_t(\lambda^*_t)$. For every integer $k\ge1$, the optimal value of the $k$-scaled problem satisfies
--
--   $$
--   \Pi_{C,k}\le k\int_0^Tr^*_t\,dt.
--   $$
--
--   So the optimal revenue grows at most linearly in the scale.
--
--   Differences from the source:
--   - generalization: prices with an invertible rate–price map on each piece → rates are chosen directly; R_t is data and no price map is modelled; reason: the page states the two are equivalent (p.5), and any such map gives this data
--   - generalization: non-anticipatory pricing policies → progressively measurable rates in any filtration whose sales compensator is ∫λ, with unit-jump sales and capacity holding almost surely, randomization allowed; reason: this class contains the paper's policies, so the supremum is over at least as much and the bounds imply the paper's
--   - reading: a_{m,n} > 0, then a positive entry in every row and column (p.5) → 0 ≤ a m n with a positive entry in every row and column; reason: the row and column condition only has content for a_{m,n} ≥ 0; the case a_{m,n} > 0 is included
--   - encoding: Poisson rates and a null price vector (Assumption 2) → Λ j lies in the nonnegative orthant and R j 0 = 0; reason: rates are nonnegative, and a null price sells nothing so it earns nothing
--   - encoding: expected revenue with instantaneous expected revenue rate R_t(λ_t) (p.6) → E∫₀ᵀ R_t(λ_t) dt, with the revenue rate integrable on [0,T]×Ω; reason: the page's objective written as an integral; a policy without expected revenue has no objective value
--   - encoding: the probability space is not named → sample spaces range over Ω : Type; reason: a universe choice; canonical path spaces live in Type
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
--   - encoding: k ∈ ℕ indexes the scaled problems (p.8) → k : ℕ with 1 ≤ k; reason: the page scales by a positive integer; at k = 0 there is no problem to speak of
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3 display, p.8

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- §3 display, p.8 (SSRN 3831496): `Π_{C,k} ≤ k · ∫₀ᵀ r*_t dt`. -/
theorem scaled_upper_bound {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l) (k : ℕ) (hk : 1 ≤ k) :
    optimalRevenue (I.scale k) ≤ k * detValue I l := by sorry

end StateIndepNRM
