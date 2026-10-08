-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_lemma_8
-- name    : VeinottSensitiveDP.Sensitive.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:16.870543+00:00
-- url     : https://prove2.me/theorems/d2e373ff-1f76-4919-b62c-037fa2a8b04e
-- title:
--   Lemma 8 — v_ρ(g, f^∞) = Σ_{n≥−1} (±ρ)ⁿ ψ_n^±(g, f) when |σ(ρH(f))| < 1 and |σ(βP(f))| < 1
-- statement:
--   In the model of §4, let $f,g\in F$, $\rho>-1$, $\rho\ne0$, $\beta=(1+\rho)^{-1}$, and suppose $|\sigma(\rho H(f))|<1$ and $|\sigma(\beta P(f))|<1$. Then, with $v_\rho(g,\pi)=r(g)+Q(g)V_\rho(\pi)-\rho V_\rho(\pi)$ and $\psi_n^\pm(g,f)$ as in (32),
--   $$v_\rho(g,f^\infty)=\sum_{n=-1}^\infty(\pm\rho)^n\,\psi_n^\pm(g,f), \tag{33}$$
--   and the series converges.
--
--   The coefficients $\psi_n^\pm(g,f)$ are thus the Laurent coefficients of the policy improvement test quantity, and $g$ improves $f$ for all small $\pm\rho>0$ exactly when their first nonzero entries are positive.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. The $n=-1$ term is written separately and the sum over $n\ge0$ is a `tsum` whose convergence is stated.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, Lemma 8, (33)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Lemma 8: if `f, g ε F`, `|σ(ρH(f))| < 1` and `|σ(βP(f))| < 1`, then
(33) `v_ρ(g, f^∞) = Σ_{n=−1}^∞ (±ρ)ⁿ ψ_n^±(g, f)`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1647, §4, Lemma 8, (33).

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; `(±ρ)ⁿ = (σρ)ⁿ`. `v_ρ(g, π) = r(g) + Q(g)V_ρ(π) − ρV_ρ(π)` is the
first expression of (30). The `n = −1` term is written separately and the rest is a `tsum` over
`n ≥ 0` whose convergence is part of the conclusion; `−1 < ρ` and `ρ ≠ 0` as in Theorem 3. -/
theorem lemma_8 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (f g : DecisionRule A) (ρ : ℝ) (hρ1 : -1 < ρ) (hρ0 : ρ ≠ 0)
    (hH : VeinottSensitiveDP.Transient.specRad (ρ • M.H f) < 1) (hP : VeinottSensitiveDP.Transient.specRad (beta ρ • M.P f) < 1) :
    Summable (fun n : ℕ => (σ * ρ) ^ n • M.ψ σ g f n) ∧
      M.vrho ρ g (stationary f) =
        (σ * ρ)⁻¹ • M.ψ σ g f (-1) + ∑' n : ℕ, (σ * ρ) ^ n • M.ψ σ g f n := by sorry

end VeinottSensitiveDP.Sensitive
