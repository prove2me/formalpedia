-- Prove2me | Theorems.Thm_TIESched_lemma_4_2
-- name    : TIESched.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:46:45.74229+00:00
-- url     : https://prove2.me/theorems/3334bbe5-89cb-4291-9603-c758bb0bc8d5
-- title:
--   Lemma 4.2 — $\mathrm{OPT}(\rho)\le\rho+m\sqrt{\rho(1-\rho)/L}$, hence $\mathrm{OPT}(\rho)\le(1+\varepsilon)\rho$
-- statement:
--   For every star template and every $\rho\in[0,1]$,
--   $$\mathrm{OPT}(\rho)\le\rho+m\sqrt{\frac{\rho(1-\rho)}{L}}.$$
--   Consequently, for every $\varepsilon>0$ and every $\rho\in(0,1]$ with $\rho\ge m^2/(\varepsilon^2L)$, $\mathrm{OPT}(\rho)\le(1+\varepsilon)\rho$.
--
--   The expected integral optimum of the random star instance falls to slope about $1$ on a scale that shrinks as $L$ grows.
--
--   Differences from the source:
--   - encoding: OPT(ρ) = E[OPT(I_ρ)] → the explicit finite sum optRho; reason: the same expectation written out
--   - encoding: vertices v_0, …, v_{m−1} and a bijection σ onto [m] → vertices Fin m with center 0 and σ : Equiv.Perm (Fin m); group labels are any pairwise disjoint sets of L natural numbers; reason: the same bijections and the same templates
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 4.2, p.15

import Mathlib
import Definitions.Def_TIESched_StarTemplate

set_option autoImplicit false

namespace TIESched

/-- **Lemma 4.2** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 4.2, p.15). For every star template and
every `ρ ∈ [0, 1]`, `OPT(ρ) ≤ ρ + m √(ρ(1 − ρ)/L)`. Consequently, for every `ε > 0` and every
`ρ ∈ (0, 1]` with `ρ ≥ m²/(ε²L)`, `OPT(ρ) ≤ (1 + ε)ρ`.

**Formalization Note.** `OPT(ρ)` is `StarTemplate.optRho`, the expectation of the optimal integral
makespan written as an explicit finite sum over bijections and job sets. -/
theorem lemma_4_2 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (T : StarTemplate m) :
    (∀ ρ ∈ Set.Icc (0 : ℝ) 1, T.optRho ρ ≤ ρ + (m : ℝ) * Real.sqrt (ρ * (1 - ρ) / T.L)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, (m : ℝ) ^ 2 / (ε ^ 2 * T.L) ≤ ρ →
        T.optRho ρ ≤ (1 + ε) * ρ := by sorry

end TIESched
