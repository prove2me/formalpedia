-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_lemma_1
-- name    : RightRepair.Equilibrium.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:34.637315+00:00
-- url     : https://prove2.me/theorems/4dcc4e52-1438-4257-b7b2-5fd1e18a2c3b
-- title:
--   Lemma 1, p. 12 — three consumer segments
-- statement:
--   Fix nonnegative new and used prices and an admissible repair price in the identical-quality repair model. Suppose each consumer type $\theta\in[0,1]$ has an average utility $\lambda(\theta)$ and state values satisfying the three Bellman equations (G.25). Then there are thresholds $\theta_1\le\theta_2$ such that
--
--   $$
--   \lambda(\theta)=\begin{cases}
--   0 & \theta<\theta_1,\\
--   \delta\theta-p_u & \theta_1\le\theta<\theta_2,\\
--   \theta-p_n+(1-f)p_u+f[p_u-\min\{c_I,p_r\}]^+ & \theta_2\le\theta.
--   \end{cases}
--   $$
--
--   These correspond respectively to inactivity, buying used each period, and buying new each period. The statement restricts consumer types to $[0,1]$; an empty segment is permitted.
--
--   **Formalization Note** The Bellman equations constrain $\lambda$; the conclusion does not follow from its definition. The nonnegative unit-cost pins are contained in the standing assumptions, and `none` denotes $p_r=\infty$.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), p. 12, Lemma 1; OA p. 17, (G.25) (PDF 50)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem lemma_1 (P : Params) (hP : Standing P)
    (pn : ℝ) (pr : Option ℝ) (pu : ℝ)
    (lam G0 G1bar G1 : ℝ → ℝ)
    (hpn : 0 ≤ pn) (hpr : repairAdmissible pr) (hpu : 0 ≤ pu)
    (hBellman : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      Bellman P pn pr pu θ (lam θ) (G0 θ) (G1bar θ) (G1 θ)) :
    ∃ θ₁ θ₂ : ℝ, θ₁ ≤ θ₂ ∧
      ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (θ < θ₁ → lam θ = 0) ∧
        (θ₁ ≤ θ → θ < θ₂ → lam θ = uUsed P pu θ) ∧
        (θ₂ ≤ θ → lam θ = uNew P pn pr pu θ) := by sorry

end RightRepair.Equilibrium
