-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_theorem_3
-- name    : VeinottSensitiveDP.Sensitive.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:53.135978+00:00
-- url     : https://prove2.me/theorems/df4a4fef-1788-4f2e-a49f-3c81e50dc96b
-- title:
--   Theorem 3 — V_ρ(f^∞) = Σ_{n≥−1} (±ρ)ⁿ y_n^±(f) when |σ(ρH(f))| < 1 and |σ(βP(f))| < 1
-- statement:
--   In the model of §4, let $f\in F$, let $\rho>-1$, $\rho\neq0$, $\beta=(1+\rho)^{-1}$, and suppose $|\sigma(\rho H(f))|<1$ and $|\sigma(\beta P(f))|<1$. Then
--   $$V_\rho(f^\infty)=\sum_{n=-1}^\infty(\pm\rho)^n\,y_n^\pm(f), \tag{29}$$
--   where $y_{-1}^\pm(f)=\pm P^*(f)r(f)$ and $y_n^\pm(f)=(\mp1)^nH(f)^{n+1}r(f)$ for $n=0,1,\dots$, and the series converges.
--
--   This Laurent expansion of the discounted return of a stationary policy about $\rho=0$ is what makes $n^\pm$ discount optimality of stationary policies a lexicographic comparison of the coefficients $y_n^\pm$.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. The $n=-1$ term $(\sigma\rho)^{-1}y_{-1}^\sigma(f)$ is written separately and the remaining sum over $n\ge0$ is a `tsum` whose convergence is stated. The hypothesis $\rho\ne0$ is implicit in the paper (the $n=-1$ term), and $\rho>-1$ is the standing range of §4.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1645, §4, Theorem 3, (29)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Theorem 3 (Laurent expansion of `V_ρ(f^∞)`): if `f ε F`, `|σ(ρH(f))| < 1` and
`|σ(βP(f))| < 1`, then
(29) `V_ρ(f^∞) = Σ_{n=−1}^∞ (±ρ)ⁿ y_n^±(f)`,
where `y_{−1}^±(f) ≡ ±P*(f)r(f)` and `y_n^±(f) ≡ (∓1)ⁿH(f)ⁿ⁺¹r(f)`, `n = 0, 1, ⋯`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1645, §4, Theorem 3, (29).

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; `(±ρ)ⁿ = (σρ)ⁿ`. The `n = −1` term
`(σρ)⁻¹ y_{−1}^σ(f)` is written separately and the rest is a `tsum` over `n ≥ 0` whose convergence is
part of the conclusion. `ρ` is real with `−1 < ρ` (the standing range of §4, so `β = (1 + ρ)⁻¹` is
defined) and `ρ ≠ 0` (the `n = −1` term `(±ρ)⁻¹` is undefined at `ρ = 0`). The spectral radii are
complexified (`specRad`). -/
theorem theorem_3 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (f : DecisionRule A) (ρ : ℝ) (hρ1 : -1 < ρ) (hρ0 : ρ ≠ 0)
    (hH : VeinottSensitiveDP.Transient.specRad (ρ • M.H f) < 1) (hP : VeinottSensitiveDP.Transient.specRad (beta ρ • M.P f) < 1) :
    Summable (fun n : ℕ => (σ * ρ) ^ n • M.y σ f n) ∧
      M.V ρ (stationary f) = (σ * ρ)⁻¹ • M.y σ f (-1) + ∑' n : ℕ, (σ * ρ) ^ n • M.y σ f n := by sorry

end VeinottSensitiveDP.Sensitive
