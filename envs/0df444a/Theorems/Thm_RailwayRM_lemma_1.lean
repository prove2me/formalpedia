-- Prove2me | Theorems.Thm_RailwayRM_lemma_1
-- name    : RailwayRM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:06.097033+00:00
-- url     : https://prove2.me/theorems/371da532-80d9-4d36-8cc5-8598d618d6bc
-- title:
--   Lemma 1: revenue loss of $\pi_1$ (corrected: needs $b^*_{u,m}<\bar b_m$)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$ with $b^*_{u,m}<\bar b_m$ for all $m$, and let $\bar r^*=\sum_n r_n(\vec x^*_n,y^*_n)$ and $R_D=\bar r^*T$. Let $R^{\pi_1}_S$ be the expected revenue of $\pi_1$, and let $\tau$ be the first hitting time (6) under $\tilde\pi_1$. Then
--   $$R_D-R^{\pi_1}_S\le\bar r^*\,\mathbb E\big[(T-\tau)^+\big]\le\bar r^*\sum_{m=1}^M\sum_{\ell=1}^L\frac{\sqrt{(\bar b_m-\lfloor b^*_{u,m}\rfloor)(1-\bar x^*_{\ell,m})k}}{2\bar x^*_{\ell,m}}.$$
--
--   This is the revenue half of the proof of Theorem 2.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - correction: no condition on b*_{u,m} → hypothesis b*_{u,m} < b̄_m for every m; reason: at b*_{u,m} = b̄_m the threshold of step 2 is 0 and π1 stops after period 1. Counterexample: L = N = M = 1, δ = 1, T = 4, k = 1, b̄ = 1, b̲ = 0, c_o = 0.1, c_s = 1, r(x, y) = x(0.1 − x) + y(3 − y) on [0, 0.3] × [0, 0.6]: the optimum has b* = b̄ and the gap is linear in κ
--   - encoding: division by x̄*_{ℓ,m} → x̄*_{ℓ,m} = 0 allowed, with x / 0 = 0 in Lean; reason: then no ticket on (ℓ, m) is sold, τ_{ℓ,m} = T and the term is truly 0
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), Lemma 1, App. p. 3, PDF p. 35

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **Lemma 1, corrected** (Manchiraju et al., SSRN 4112672 (2023-08-22), Lemma 1, App. p. 3, PDF
p. 35): `R_D - R^{π₁}_S ≤ r̄* E[(T - τ)⁺] ≤ r̄* ∑_m ∑_ℓ √((b̄_m - ⌊b*_{u,m}⌋)(1 - x̄*_{ℓ,m}) k) / (2 x̄*_{ℓ,m})`.

**Formalization Note.** The hypothesis `b*_{u,m} < b̄_m` for every `m` is added: without it the
threshold of step 2 of `π₁` is `0` and the bound fails. `τ` is computed under `π̃₁`, whose law is the
expectation under `staticRates`. Terms with `x̄*_{ℓ,m} = 0` are `0` because `x / 0 = 0` in Lean,
which is their true contribution, since then `τ_{ℓ,m} = T`. -/
theorem lemma_1 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (hb : ∀ m, b m < (I.bMax m : ℝ)) :
    I.detRevenue v - I.revenue (I.pi1Rates v b) ≤
        I.rbar v * I.expect (I.staticRates v)
          (fun ω => max ((I.T : ℝ) - (I.firstHitTime b (I.observe ω) : ℝ)) 0) ∧
      I.rbar v * I.expect (I.staticRates v)
          (fun ω => max ((I.T : ℝ) - (I.firstHitTime b (I.observe ω) : ℝ)) 0) ≤
        I.rbar v * ∑ m, ∑ ℓ : Fin L,
          Real.sqrt (((I.bMax m : ℝ) - (⌊b m⌋ : ℝ)) * (1 - I.xbar v ℓ m) * (I.k : ℝ)) /
            (2 * I.xbar v ℓ m) := by sorry

end RailwayRM
