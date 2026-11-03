-- Prove2me | Theorems.Thm_RelaxedIndexability_value_affine_in_subsidy
-- name    : RelaxedIndexability.value_affine_in_subsidy
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:41.932797+00:00
-- url     : https://prove2.me/theorems/9c4962f3-79f8-445a-9b52-42183e05e4f3
-- title:
--   Remark after Lemma 3 — (38), and $\hat V_{\beta,m}$ is affine in $m$ with slope the passive time
-- statement:
--   Let an arm have a row-stochastic transition matrix $\mathbf P$ with rows $p_0,\dots,p_{K-1}$ and rewards $B$, let $0<\beta<1$ and let the belief $\omega$ be fixed as a point in the threshold. Then:
--
--   1. **(38).** If $L(\omega, \omega) = n$ is finite, then for every subsidy $m$
--   $$
--   \hat V_{\beta,m}(\omega) = \frac{1-\beta^{n}}{1-\beta}\, m + \beta^{n}\Big(\mathcal T^{n}(\omega) B' + \beta\, \mathcal T^{n}(\omega)\big(\hat V_{\beta,m}(p_0), \dots, \hat V_{\beta,m}(p_{K-1})\big)'\Big),
--   $$
--   with $\mathcal T^n(\omega) = \omega\mathbf P^n$; if $L(\omega,\omega) = +\infty$, then $\hat V_{\beta,m}(\omega) = m/(1-\beta)$.
--   2. **Linearity in $m$.** For every belief $x$ in the simplex (in particular $x = \omega$ and $x = p_k$) and every $m$,
--   $$
--   \hat V_{\beta,m}(x) = \hat V_{\beta,0}(x) + m\, \hat D_\beta(x),
--   $$
--   where $\hat D_\beta(x)$ is the expected total discounted passive time of the threshold policy started at $x$.
--
--   So the coefficient of $m$ in the value of the threshold policy is its passive time, which is what makes the indifference equation (37) affine in $m$.
--
--   Differences from the source:
--   - reading: (38) with L(ω,ω) = +∞ → V̂_{β,m}(ω) = m/(1−β); reason: β^{+∞} = 0.
--   - reading: "a linear function of m" → an affine function of m, V̂_{β,m} = V̂_{β,0} + m·(slope); reason: (38) has the m-independent term β^{L}(T^{L}(ω)B′ + …), so "linear" means affine.
--   - generalization: V̂(ω) and V̂(p_k) linear in m, the coefficient for V̂(ω) being the passive time → V̂_{β,m}(x) = V̂_{β,0}(x) + m D̂_β(x) for every belief x in the simplex; reason: x = ω and x = p_k give the source's claims (and the coefficient for V̂(p_k) as well).
--   - generalization: the standing assumptions P irreducible and aperiodic (p.7) and 0 = B₀ ≤ ⋯ ≤ B_{K−1} (p.11) → not assumed; reason: not used; the statement for every row-stochastic P and every B contains the source's case.
--   - encoding: V̂ is the expected total discounted reward of π_{β,m} → the limit of the n-horizon expected discounted rewards computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
--   - encoding: D̂ is the expected total discounted passive time under π_{β,m} → the limit of the n-horizon expected discounted passive times (reward 1 passive, 0 active) computed by conditioning on the observations (4); reason: the same quantity, the limit exists for 0 < β < 1.
--   - encoding: the passive time D̂_{β,m} → passiveTime without an m argument; reason: the threshold rule (33) does not involve m, so D̂_{β,m} = D̂_β for every m (stated on p.22).
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, Remark after Lemma 3, second bullet, (38), p.21

import Mathlib
import Definitions.Def_RelaxedIndexability_crossTime
import Definitions.Def_RelaxedIndexability_thresholdValue
import Definitions.Def_RelaxedIndexability_passiveTime

open Matrix

namespace RelaxedIndexability

/-- **The value at the threshold, (38), and linearity in the subsidy** (Liu, arXiv:2107.11939v4,
Remark after Lemma 3, second bullet, with (38), p.21). Fix `ω` as a point in the threshold.

1. (38): if `L(ω, ω) = n` is finite, then
   `V̂_{β,m}(ω) = (1 − βⁿ)/(1 − β) m + βⁿ (ωPⁿB′ + β ωPⁿ (V̂_{β,m}(p₀), …, V̂_{β,m}(p_{K−1}))′)`;
   if `L(ω, ω) = +∞`, then `V̂_{β,m}(ω) = m/(1 − β)`.
2. For every belief `x` in the simplex (in particular `x = ω` and `x = p_k`), `V̂_{β,m}(x)` is an
   affine function of `m` whose coefficient of `m` is the expected total discounted passive time
   `D̂_β(x)`: `V̂_{β,m}(x) = V̂_{β,0}(x) + m D̂_β(x)`. -/
theorem value_affine_in_subsidy {K : ℕ} (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Matrix (Fin K) (Fin K) ℝ) (hP : P ∈ Matrix.rowStochastic ℝ (Fin K)) (B : Fin K → ℝ)
    (ω : Fin K → ℝ) (hω : ω ∈ stdSimplex ℝ (Fin K)) :
    (∀ n : ℕ, crossTime P B ω ω = n → ∀ m : ℝ,
      thresholdValue β P B ω m ω =
        (1 - β ^ n) / (1 - β) * m
          + β ^ n * ((ω ᵥ* P ^ n) ⬝ᵥ B
            + β * ((ω ᵥ* P ^ n) ⬝ᵥ fun j => thresholdValue β P B ω m (P j)))) ∧
    (crossTime P B ω ω = ⊤ → ∀ m : ℝ, thresholdValue β P B ω m ω = m / (1 - β)) ∧
    (∀ x ∈ stdSimplex ℝ (Fin K), ∀ m : ℝ,
      thresholdValue β P B ω m x = thresholdValue β P B ω 0 x + m * passiveTime β P B ω x) := by sorry

end RelaxedIndexability
