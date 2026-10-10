-- Prove2me | Theorems.Thm_WassMMSE_FW_beta_le_betaBar
-- name    : WassMMSE.FW.beta_le_betaBar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:10.847557+00:00
-- url     : https://prove2.me/theorems/3a25d999-cbe4-4cd2-b46a-c2844d93ae38
-- title:
--   Proof of Theorem 6.2, p. 25 — along Algorithm 1, β_t ≤ β̄ = max{τβ, β₋₁} for all t
-- statement:
--   In the setting of Section 6.1, assume that $f$ is $\beta$-smooth on $\mathcal S$ (Assumption 6.1 (i)), and let $(s_t,\beta_t,\eta_t)_{t\ge0}$ be a run of the fully adaptive Frank-Wolfe algorithm (Algorithm 1) with inputs $s_0\in\mathcal S$, $\beta_{-1}>0$, $\tau>1$, $\zeta>1$. Then the smoothness parameters selected by the line search stay bounded:
--
--   $$\beta_t\le\bar\beta=\max\{\tau\beta,\ \beta_{-1}\}\qquad\forall t\ge0.$$
--
--   This bound turns the per-iteration contraction factor, which depends on $\beta_t$, into the uniform rate of Theorem 6.2. It relies on $\beta_t$ being the *smallest* accepted element of $(\beta_{t-1}/\zeta)\cdot\{1,\tau,\tau^2,\dots\}$.
--
--   **Formalization Note** The page cites this bound from its reference [59, Proposition 2]; it is stated here for every $t\ge0$.
-- source:
--   Nguyen, Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, arXiv:1911.03539v2, p. 25, proof of Theorem 6.2, after (6.12) (citing [59, Proposition 2])

import Mathlib
import Definitions.Def_WassMMSE_FW_Setting

namespace WassMMSE.FW

open scoped RealInnerProductSpace

/-- Proof of Theorem 6.2, p. 25 ("β_t ≤ β̄ for all t ∈ ℕ", citing [59, Proposition 2]): under
Assumption 6.1 (i), every run of Algorithm 1 has `β_t ≤ β̄ = max{τβ, β_{−1}}` for all `t`. -/
theorem beta_le_betaBar
    {K : ℕ} {d : Fin K → ℕ} {S : Set (BlockSpace K d)}
    {Sk : (k : Fin K) → Set (EuclideanSpace ℝ (Fin (d k)))}
    {f : BlockSpace K d → ℝ} {F : BlockSpace K d → BlockSpace K d} {δ : ℝ}
    (hS : IsBlockFeasibleSet S Sk) (hf : IsConvexDiffObjective S f)
    (hF : IsInexactOracle S f F δ)
    {β : ℝ} (hβ : IsSmoothOn S f β)
    {βm1 τ ζ : ℝ} {s : ℕ → BlockSpace K d} {βt ηt : ℕ → ℝ}
    (hrun : IsFAFWRun S f F βm1 τ ζ s βt ηt) :
    ∀ t : ℕ, βt t ≤ max (τ * β) βm1 := by sorry

end WassMMSE.FW
