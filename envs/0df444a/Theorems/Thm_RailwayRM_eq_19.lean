-- Prove2me | Theorems.Thm_RailwayRM_eq_19
-- name    : RailwayRM.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:06.184839+00:00
-- url     : https://prove2.me/theorems/2a46d03f-d063-4856-bca2-42e161b11c74
-- title:
--   Inequality (19): shortfall of the hitting time (corrected: needs $b^*_{u,m}<\bar b_m$)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$, let $\ell$ be a leg and $m$ a train with $b^*_{u,m}<\bar b_m$. Under the relaxed static policy $\tilde\pi_1$, the hitting time $\tau_{\ell,m}$ satisfies
--   $$\mathbb E\big[(T-\tau_{\ell,m})^+\big]\le\frac{\sqrt{(\bar b_m-\lfloor b^*_{u,m}\rfloor)(1-\bar x^*_{\ell,m})k}}{2\bar x^*_{\ell,m}}.$$
--
--   This bounds how early reserved sales on a leg exhaust their limit, using only the mean and the variance of the hitting time.
--
--   **Formalization Note.** If $\bar x^*_{\ell,m}=0$ the right side is $0$ in Lean, and the left side is $0$ too because $\tau_{\ell,m}=T$.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - correction: no condition on b*_{u,m} → hypothesis b*_{u,m} < b̄_m for this train m; reason: at b*_{u,m} = b̄_m the threshold is 0, so τ_{ℓ,m} = 1 while feasibility forces x̄*_{ℓ,m} = 0 and the right side divides by 0. Counterexample: the instance of the corrected Theorem 2 with T = 4, where the left side is 3
--   - encoding: division by x̄*_{ℓ,m} → x̄*_{ℓ,m} = 0 allowed, with x / 0 = 0 in Lean; reason: then no ticket on (ℓ, m) is sold, τ_{ℓ,m} = T and the term is truly 0
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (19), App. p. 4, PDF p. 36

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **Inequality (19)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (19), App. p. 4, PDF p. 36):
under `π̃₁`, `E[(T - τ_{ℓ,m})⁺] ≤ √((b̄_m - ⌊b*_{u,m}⌋)(1 - x̄*_{ℓ,m}) k) / (2 x̄*_{ℓ,m})`.

**Formalization Note.** The hypothesis `b*_{u,m} < b̄_m` for this train is a correction: at
`b*_{u,m} = b̄_m` the threshold is `0`, so `τ_{ℓ,m} = 1` while `x̄*_{ℓ,m} = 0` and the right side
is undefined. Under it the threshold is at least `k ≥ 1`. When
`x̄*_{ℓ,m} = 0`, no reserved ticket on `(ℓ, m)` is sold, `τ_{ℓ,m} = T`, the left side is `0`, and the
right side is `0` because `x / 0 = 0` in Lean. -/
theorem eq_19 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (ℓ : Fin L) (m : Fin M)
    (hbm : b m < (I.bMax m : ℝ)) :
    I.expect (I.staticRates v) (fun ω => max ((I.T : ℝ) - (I.hitTime b ℓ m (I.observe ω) : ℝ)) 0) ≤
      Real.sqrt (((I.bMax m : ℝ) - (⌊b m⌋ : ℝ)) * (1 - I.xbar v ℓ m) * (I.k : ℝ)) /
        (2 * I.xbar v ℓ m) := by sorry

end RailwayRM
