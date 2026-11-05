-- Prove2me | Theorems.Thm_StateIndepNRM_eq_1
-- name    : StateIndepNRM.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:50.625173+00:00
-- url     : https://prove2.me/theorems/8ae086e9-1750-46fb-b907-c8adb5483807
-- title:
--   (1), p.7 — $\Pi_C\le\int_0^Tr^*_t\,dt$
-- statement:
--   Let $(\lambda^*_t)$ be an optimal solution of the deterministic problem $\mathbb P_{\mathrm{Det}}$, with $r^*_t=R_t(\lambda^*_t)$. Every admissible policy has expected revenue at most $\int_0^Tr^*_t\,dt$, so the set of expected revenues is bounded above and
--
--   $$
--   \Pi_C\le\int_0^Tr^*_t\,dt.
--   $$
--
--   This is the upper bound against which the make-to-stock policy is compared.
--
--   **Formalization Note** The paper cites this from Gallego and van Ryzin (1997). No closedness of $\Lambda_j$ or continuity of $R_j$ is assumed.
--
--   Differences from the source:
--   - generalization: prices with an invertible rate–price map on each piece → rates are chosen directly; R_t is data and no price map is modelled; reason: the page states the two are equivalent (p.5), and any such map gives this data
--   - generalization: non-anticipatory pricing policies → progressively measurable rates in any filtration whose sales compensator is ∫λ, with unit-jump sales and capacity holding almost surely, randomization allowed; reason: this class contains the paper's policies, so the supremum is over at least as much and the bounds imply the paper's
--   - reading: a_{m,n} > 0, then a positive entry in every row and column (p.5) → 0 ≤ a m n with a positive entry in every row and column; reason: the row and column condition only has content for a_{m,n} ≥ 0; the case a_{m,n} > 0 is included
--   - encoding: Poisson rates and a null price vector (Assumption 2) → Λ j lies in the nonnegative orthant and R j 0 = 0; reason: rates are nonnegative, and a null price sells nothing so it earns nothing
--   - encoding: expected revenue with instantaneous expected revenue rate R_t(λ_t) (p.6) → E∫₀ᵀ R_t(λ_t) dt, with the revenue rate integrable on [0,T]×Ω; reason: the page's objective written as an integral; a policy without expected revenue has no objective value
--   - encoding: the probability space is not named → sample spaces range over Ω : Type; reason: a universe choice; canonical path spaces live in Type
--   - generalization: Π_C ≤ ∫₀ᵀ r*_t dt → the same bound, with the bound for each admissible policy and BddAbove of the value set as further clauses; reason: these give the sSup bound its meaning, and the printed inequality is the last clause
--   - encoding: resources 1..M, products 1..N, finite sub-intervals of [0,T] with no owner for a breakpoint, processes on [0,T] → Fin M and Fin N (0-based); half-open pieces with the last one closed; filtrations and martingales indexed by Set.Icc 0 T; reason: a relabelling, a choice on a null set of times, and nothing is required after T; no instance changes
--   - encoding: an optimal solution (λ*_t) of P_Det (p.6) → a measurable l with integrable coordinates and integrable revenue rate, optimal among such functions; reason: the page's integrals presuppose this of every solution
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, (1), p.7

import Mathlib
import Definitions.Def_StateIndepNRM_mtsPolicy

open MeasureTheory Set

namespace StateIndepNRM

/-- (1), p.7 (Manchiraju–Dawande–Janakiraman, SSRN 3831496): `Π_C ≤ ∫₀ᵀ r*_t dt`. Every admissible
policy earns at most the fluid optimum, so the value set is bounded above and `Π_C` is at most the
fluid optimum.

**Formalization Note.** The paper cites this from Gallego and van Ryzin (1997). The pointwise form and
`BddAbove` are stated with the `sSup` bound, because the real `sSup` means nothing without them. -/
theorem eq_1 {M N : ℕ} (I : Instance M N) (l : ℝ → Fin N → ℝ) (hl : IsDetOptimal I l) :
    (∀ {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (sys : PricingSystem I.T N mΩ), IsAdmissible I P sys → revenue I P sys ≤ detValue I l) ∧
    BddAbove (valueSet I) ∧ optimalRevenue I ≤ detValue I l := by sorry

end StateIndepNRM
